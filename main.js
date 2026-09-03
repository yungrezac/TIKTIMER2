const { app, BrowserWindow, ipcMain, net } = require('electron');
const path = require('path');
const fs = require('fs');
const WebSocket = require('ws'); 
const { execSync } = require('child_process');
const os = require('os');
const crypto = require('crypto');
const { WebcastPushConnection } = require('tiktok-live-connector');

// Пытаемся загрузить socket.io-client для мультиплеера
let ioClient = null;
try {
    ioClient = require('socket.io-client');
} catch (e) {
    console.error("socket.io-client не установлен! Мультиплеер работать не будет. Выполните: npm install socket.io-client");
}

app.commandLine.appendSwitch('disable-renderer-backgrounding');
app.commandLine.appendSwitch('disable-background-timer-throttling');
app.commandLine.appendSwitch('disable-backgrounding-occluded-windows');
app.commandLine.appendSwitch('disable-features', 'CalculateNativeWinOcclusion');
// УДАЛЕНО: disable-frame-rate-limit (Именно он жрал 20% CPU, заставляя прозрачные окна рендериться на 1000+ FPS)
app.commandLine.appendSwitch('enable-gpu-rasterization');
app.commandLine.appendSwitch('ignore-gpu-blocklist');
app.commandLine.appendSwitch('enable-zero-copy');
app.commandLine.appendSwitch('disable-software-rasterizer');

const windowBoundsPath = path.join(app.getPath('userData'), 'window-bounds.json');

function getMachineId() {
    let id = '';
    try {
        if (process.platform === 'win32') {
            id = execSync('wmic csproduct get uuid').toString().split('\n')[1].trim();
        } else if (process.platform === 'darwin') {
            id = execSync('ioreg -rd1 -c IOPlatformExpertDevice | grep IOPlatformUUID').toString().split('"')[3];
        } else {
            id = execSync('cat /etc/machine-id').toString().trim();
        }
    } catch (e) {
        id = crypto.createHash('sha256').update(os.userInfo().username + os.hostname()).digest('hex');
    }
    return id;
}

ipcMain.handle('get-machine-id', async () => {
    return getMachineId();
});

function getSavedBounds(name, defaultBounds) {
    try {
        if (fs.existsSync(windowBoundsPath)) {
            const data = JSON.parse(fs.readFileSync(windowBoundsPath, 'utf8'));
            if (data[name]) return data[name];
        }
    } catch (e) {}
    return defaultBounds;
}

function saveBounds(name, bounds) {
    try {
        let data = {};
        if (fs.existsSync(windowBoundsPath)) {
            data = JSON.parse(fs.readFileSync(windowBoundsPath, 'utf8'));
        }
        data[name] = bounds;
        fs.writeFileSync(windowBoundsPath, JSON.stringify(data));
    } catch (e) {}
}

let mainWindow;
let remoteWindow;
let timerWindow;
let rouletteWindow;
let uptimeWindow; 
let tiktokConnection = null;

let currentUsername = ''; 
let reconnectTimeout = null; 
let isConnecting = false;
let activeTikTokUsername = null;

let daWs = null;
let isDAConnecting = false;
let daStatusText = 'Ожидание';
let ttStatusText = 'Ожидание';
let isTtActive = false;
const daTokenPath = path.join(app.getPath('userData'), 'da_token.json');

let dpInterval = null;
let dxInterval = null;
let dpStatusText = 'Ожидание';
let dxStatusText = 'Ожидание';
let lastDpDonationId = null;
let dxProcessedIds = new Set();

let mpSocket = null;
let mpRoomId = null;
let mpUsers = [];
const mpFailedCache = new Set(); // ОПТИМИЗАЦИЯ: Теперь он используется

// НОВОЕ: Постоянный кэш профилей (сохранение на диск)
const profileCachePath = path.join(app.getPath('userData'), 'profile_cache.json');
let mpUserCache = {};
try {
    if (fs.existsSync(profileCachePath)) {
        mpUserCache = JSON.parse(fs.readFileSync(profileCachePath, 'utf8'));
    }
} catch (e) {
    mpUserCache = {};
}

function saveProfileCache() {
    try {
        fs.writeFileSync(profileCachePath, JSON.stringify(mpUserCache));
    } catch (e) {}
}

let topDonators = {};
let topLikers = {};

let broadcastTimeTimeout = null;
function requestBroadcastTime() {
    if (broadcastTimeTimeout) return;
    broadcastTimeTimeout = setTimeout(() => {
        broadcastTime();
        broadcastTimeTimeout = null;
    }, 100); 
}

let broadcastTopsTimeout = null;
function requestBroadcastTops() {
    if (broadcastTopsTimeout) return;
    broadcastTopsTimeout = setTimeout(() => {
        broadcastTops();
        broadcastTopsTimeout = null;
    }, 1000); 
}

async function getTikTokProfile(username) {
    let win = new BrowserWindow({
        width: 450,
        height: 600,
        show: false,
        alwaysOnTop: true,
        webPreferences: {
            nodeIntegration: false,
            contextIsolation: true,
            images: true
        }
    });

    win.webContents.userAgent = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36';

    try {
        console.log(`[DEBUG-PROFILE] Запуск окна для: ${username}`);
        
        try {
            await win.loadURL(`https://www.tiktok.com/@${username}`);
        } catch (navError) {
            console.log(`[DEBUG-PROFILE] Предупреждение при загрузке:`, navError.message);
        }

        let attempts = 0;
        const maxAttempts = 120;
        let captchaShown = false;

        while (attempts < maxAttempts) {
            if (win.isDestroyed()) return null;

            const result = await win.webContents.executeJavaScript(`
                (() => {
                    function extract() {
                        let nickname = null;
                        let avatar = null;
                        let method = 'none';

                        const scriptNode = document.querySelector('#__UNIVERSAL_DATA_FOR_REHYDRATION__') || document.querySelector('#SIGI_STATE');
                        
                        if (scriptNode) {
                            try {
                                const data = JSON.parse(scriptNode.innerHTML);
                                
                                try {
                                    const userObj = data?.__DEFAULT_SCOPE__?.['webapp.user-detail']?.userInfo?.user;
                                    if (userObj) {
                                        nickname = userObj.nickname;
                                        avatar = userObj.avatarLarger || userObj.avatarMedium || userObj.avatarThumb;
                                        method = 'json_direct';
                                        if (nickname && avatar) return { nickname, avatar, method };
                                    }
                                } catch(e) {}
                                
                                function findKeys(obj) {
                                    if (!obj || typeof obj !== 'object') return;
                                    if (!nickname && obj.nickname && typeof obj.nickname === 'string') nickname = obj.nickname;
                                    if (!avatar) {
                                        if (obj.avatarLarger && typeof obj.avatarLarger === 'string') avatar = obj.avatarLarger;
                                        else if (obj.avatarMedium && typeof obj.avatarMedium === 'string') avatar = obj.avatarMedium;
                                        else if (obj.avatarThumb && typeof obj.avatarThumb === 'string') avatar = obj.avatarThumb;
                                        else if (obj.avatar_larger && obj.avatar_larger.url_list?.length > 0) avatar = obj.avatar_larger.url_list[0];
                                    }
                                    if (nickname && avatar) return;
                                    for (const key in obj) {
                                        if (Object.prototype.hasOwnProperty.call(obj, key)) {
                                            findKeys(obj[key]);
                                            if (nickname && avatar) return;
                                        }
                                    }
                                }
                                
                                findKeys(data);
                                if (nickname || avatar) method = 'json_deep';
                            } catch (e) {}
                        }

                        // УЛУЧШЕННЫЙ ПОИСК НИКНЕЙМА: берем строго user-title (Отображаемое имя)
                        const titleEl = document.querySelector('[data-e2e="user-title"]');
                        if (titleEl && titleEl.innerText) {
                            const domNick = titleEl.innerText.trim();
                            if (domNick) {
                                nickname = domNick;
                                method += '+dom_title';
                            }
                        } else if (!nickname) {
                            // Резервный вариант, если вдруг заголовка нет
                            const subtitleEl = document.querySelector('[data-e2e="user-subtitle"]');
                            if (subtitleEl && subtitleEl.innerText) {
                                nickname = subtitleEl.innerText.replace('@', '').trim();
                                method += '+dom_sub';
                            }
                        }
                        
                        if (!avatar) {
                            const imgEl = document.querySelector('[data-e2e="user-avatar"] img');
                            if (imgEl && imgEl.src) { avatar = imgEl.src; method += '+dom_avatar'; }
                        }

                        return { nickname, avatar, method };
                    }

                    const successEl = document.querySelector('#__UNIVERSAL_DATA_FOR_REHYDRATION__') || 
                                      document.querySelector('#SIGI_STATE') || 
                                      document.querySelector('[data-e2e="user-title"]') ||
                                      document.querySelector('[data-e2e="user-subtitle"]');
                    
                    if (successEl) {
                        const data = extract();
                        if (data.nickname || data.avatar) return { status: 'success', data };
                    }

                    const errorEl = document.querySelector('[data-e2e="error-title"]');
                    if (errorEl) return { status: 'not_found' };

                    const hasCaptcha = document.getElementById('captcha_container') || 
                                       document.getElementById('captcha-verify-image') ||
                                       document.querySelector('[class*="captcha"]') || 
                                       window.location.href.includes('captcha') || 
                                       window.location.href.includes('verify') ||
                                       document.getElementById('verify-ele');

                    if (hasCaptcha) return { status: 'captcha' };

                    return { status: 'loading' };
                })();
            `);

            if (result.status === 'success') {
                console.log(`[DEBUG-PROFILE] Успешно получены данные:`, result.data);
                if (captchaShown && !win.isDestroyed()) {
                    win.hide();
                }
                return result.data;
            } else if (result.status === 'not_found') {
                console.log(`[DEBUG-PROFILE] Пользователь не найден.`);
                return null;
            } else if (result.status === 'captcha') {
                if (!captchaShown && !win.isDestroyed()) {
                    console.log(`[DEBUG-PROFILE] ⚠️ ОБНАРУЖЕНА КАПЧА! Показываем окно для ручного решения...`);
                    win.show();
                    win.focus();
                    captchaShown = true;
                    updateTtStatus('РЕШИТЕ КАПЧУ В ОТКРЫТОМ ОКНЕ!', false);
                }
            }

            attempts++;
            await new Promise(r => setTimeout(r, 500));
        }

        console.log(`[DEBUG-PROFILE] Таймаут получения профиля (60 сек).`);
        return null;

    } catch (error) {
        console.error(`[DEBUG-PROFILE] Ошибка при получении профиля ${username}:`, error);
        return null;
    } finally {
        if (win && !win.isDestroyed()) {
            win.close();
        }
    }
}

// ОПТИМИЗАЦИЯ CPU: Используем mpFailedCache и постоянный профиль кэш
async function enrichMpUsers(users) {
    let changed = false;
    for (let u of users) {
        const cleanUsername = (u.username || '').replace('@', '');
        const cleanCurrent = (currentUsername || '').replace('@', '');
        
        if (cleanUsername === cleanCurrent && currentStreamerInfo.avatar && !currentStreamerInfo.avatar.includes('1055823.png')) {
            if (u.avatar !== currentStreamerInfo.avatar || u.nickname !== currentStreamerInfo.username) {
                u.avatar = currentStreamerInfo.avatar;
                u.nickname = currentStreamerInfo.username;
                changed = true;
            }
            continue;
        }

        if (u.avatar && !u.avatar.includes('2952338.png') && !u.avatar.includes('1055823.png')) {
            mpUserCache[cleanUsername] = { nickname: u.nickname || cleanUsername, avatar: u.avatar };
            saveProfileCache();
            continue;
        }

        if (!u.avatar || !u.nickname || u.avatar.includes('2952338.png')) {
            if (mpUserCache[cleanUsername]) {
                u.avatar = mpUserCache[cleanUsername].avatar;
                u.nickname = mpUserCache[cleanUsername].nickname;
                changed = true;
            } else if (!mpFailedCache.has(cleanUsername)) { 
                const info = await getTikTokProfile(cleanUsername);
                if (info && (info.nickname || info.avatar)) {
                    u.avatar = info.avatar || u.avatar;
                    u.nickname = info.nickname || u.nickname;
                    mpUserCache[cleanUsername] = { nickname: u.nickname, avatar: u.avatar };
                    saveProfileCache(); // Сохраняем в файл
                    changed = true;
                } else {
                    mpFailedCache.add(cleanUsername);
                }
            }
        }
    }
    if (changed) {
        broadcastMpStatus();
    }
}

function broadcastTops() {
    const sortedCoins = Object.values(topDonators).sort((a, b) => b.amount - a.amount).slice(0, 50);
    const sortedLikes = Object.values(topLikers).sort((a, b) => b.amount - a.amount).slice(0, 50);
    const payload = { coins: sortedCoins, likes: sortedLikes };
    
    if (remoteWindow && !remoteWindow.isDestroyed()) remoteWindow.webContents.send('top-update', payload);
}

function updateTopDonators(username, avatar, coins) {
    if (!topDonators[username]) topDonators[username] = { username, avatar, amount: 0 };
    topDonators[username].amount += coins;
    topDonators[username].avatar = avatar;
    requestBroadcastTops(); 
}

function updateTopLikers(username, avatar, likes) {
    if (!topLikers[username]) topLikers[username] = { username, avatar, amount: 0 };
    topLikers[username].amount += likes;
    topLikers[username].avatar = avatar;
    requestBroadcastTops(); 
}

ipcMain.on('request-tops', (e) => {
    const sortedCoins = Object.values(topDonators).sort((a, b) => b.amount - a.amount).slice(0, 50);
    const sortedLikes = Object.values(topLikers).sort((a, b) => b.amount - a.amount).slice(0, 50);
    e.reply('top-update', { coins: sortedCoins, likes: sortedLikes });
});

function broadcastMpStatus(errorMsg = null) {
    const payload = {
        isConnected: mpSocket && mpSocket.connected,
        roomId: mpRoomId,
        users: mpUsers,
        error: errorMsg
    };
    BrowserWindow.getAllWindows().forEach(win => {
        if (!win.isDestroyed()) win.webContents.send('mp-status', payload);
    });
}

function updateTtStatus(text, active) {
    ttStatusText = text;
    if (active !== undefined) isTtActive = active;
    
    const payload = { 
        text: ttStatusText, 
        isActive: isTtActive,
        avatar: currentStreamerInfo.avatar,
        nickname: currentStreamerInfo.username
    };

    if (mainWindow && !mainWindow.isDestroyed()) {
        mainWindow.webContents.send('tiktok-status', payload);
    }
    
    if (mpSocket && mpSocket.connected) {
        mpSocket.emit('stream_status', { isActive: isTtActive });
    }
}

function updateDaStatus(text) {
    daStatusText = text;
    if (mainWindow && !mainWindow.isDestroyed()) mainWindow.webContents.send('da-status', text);
}

function updateDpStatus(text) {
    dpStatusText = text;
    if (mainWindow && !mainWindow.isDestroyed()) mainWindow.webContents.send('dp-status', text);
}

function updateDxStatus(text) {
    dxStatusText = text;
    if (mainWindow && !mainWindow.isDestroyed()) mainWindow.webContents.send('dx-status', text);
}

function saveDaToken(token) {
    try { fs.writeFileSync(daTokenPath, JSON.stringify({ token })); } catch(e) {}
}

function loadDaToken() {
    try { if (fs.existsSync(daTokenPath)) return JSON.parse(fs.readFileSync(daTokenPath)).token; } catch(e) {}
    return null;
}

function clearDaToken() {
    try { if (fs.existsSync(daTokenPath)) fs.unlinkSync(daTokenPath); } catch(e) {}
}

let multiplierState = { isActive: false, type: 'buff', value: 1, timeLeft: 0 };
let rouletteQueue = [];
let isRouletteBusy = false;

let ruinerQueue = [];
let isRuinerPaused = false;
let ruinerState = {
    isActive: false,
    timeLeft: 0,
    user: { username: '', avatar: '' }
};

let timerState = {
    timeLeft: 0,
    isRunning: false,
    isVictory: false,
    isBonusPhase: false,     
    isRollingBonus: false,   
    bonusTriggerUser: '',
    forceVictory: false,   
    isFrozen: false,       
    freezeTimeLeft: 0,     
    isReversed: false, 
    settings: {},
    subbedUsers: new Set(),
    userLikes: {}
};

let lastProcessedLikesMilestones = {}; 
let currentStreamTotalLikes = 0; 
let currentStreamerInfo = { username: 'Стример', avatar: 'https://cdn-icons-png.flaticon.com/512/1055/1055823.png' };

function checkIds(idsArray, giftId) {
    if (!Array.isArray(idsArray)) return false;
    return idsArray.some(id => id == giftId); 
}

function isMatched(isEnabled, giftIds, triggerDonationAmount, incomingGiftId, incomingDonationAmount) {
    if (isEnabled === false) return false;
    if (incomingGiftId && checkIds(giftIds, incomingGiftId)) return true;
    if (incomingDonationAmount !== undefined && incomingDonationAmount !== null && triggerDonationAmount) {
        if (Number(incomingDonationAmount) === Number(triggerDonationAmount)) return true;
    }
    return false;
}

function createMainWindow() {
    const bounds = getSavedBounds('main', { width: 1250, height: 850 });
    mainWindow = new BrowserWindow({
        ...bounds,
        webPreferences: { nodeIntegration: true, contextIsolation: false, backgroundThrottling: false },
        autoHideMenuBar: true, title: "MARFALEY"
    });
    mainWindow.loadFile('app.html');
    mainWindow.on('close', () => saveBounds('main', mainWindow.getBounds()));
    mainWindow.on('closed', () => { app.quit(); });
}

function createRemoteWindow() {
    if (remoteWindow) { remoteWindow.focus(); return; }
    const bounds = getSavedBounds('remote', { width: 450, height: 750 });
    remoteWindow = new BrowserWindow({
        ...bounds,
        webPreferences: { nodeIntegration: true, contextIsolation: false, backgroundThrottling: false },
        autoHideMenuBar: true, title: "Пульт"
    });
    remoteWindow.loadFile('remote.html');
    remoteWindow.on('close', () => saveBounds('remote', remoteWindow.getBounds()));
    remoteWindow.on('closed', () => { 
        remoteWindow = null; 
        topDonators = {};
        topLikers = {};
    });
}

function createTimerWindow() {
    if (timerWindow) { timerWindow.focus(); return; }
    const bounds = getSavedBounds('timer', { width: 1400, height: 800 });
    timerWindow = new BrowserWindow({
        ...bounds,
        transparent: true, frame: false, alwaysOnTop: false, title: "Таймер",
        webPreferences: { nodeIntegration: true, contextIsolation: false, backgroundThrottling: false }
    });
    timerWindow.loadFile('timer.html');
    timerWindow.on('close', () => saveBounds('timer', timerWindow.getBounds()));
    timerWindow.on('closed', () => { timerWindow = null; });
}

function createRouletteWindow() {
    if (rouletteWindow) { rouletteWindow.focus(); return; }
    const bounds = getSavedBounds('roulette', { width: 1400, height: 850 });
    rouletteWindow = new BrowserWindow({
        ...bounds,
        transparent: true, frame: false, alwaysOnTop: false, title: "Рулетка",
        webPreferences: { nodeIntegration: true, contextIsolation: false, backgroundThrottling: false }
    });
    rouletteWindow.loadFile('roulette.html');
    rouletteWindow.on('close', () => saveBounds('roulette', rouletteWindow.getBounds()));
    rouletteWindow.on('closed', () => { rouletteWindow = null; });
}

function createUptimeWindow(startTime, rouletteId) {
    if (uptimeWindow) { uptimeWindow.focus(); return; }
    const bounds = getSavedBounds('uptime', { width: 450, height: 400 });
    uptimeWindow = new BrowserWindow({
        ...bounds,
        transparent: true, frame: false, alwaysOnTop: false, title: "Время стрима",
        webPreferences: { nodeIntegration: true, contextIsolation: false, backgroundThrottling: false }
    });
    uptimeWindow.loadFile('uptime.html', { search: `startTime=${encodeURIComponent(startTime)}&rouletteId=${encodeURIComponent(rouletteId)}` });
    uptimeWindow.on('close', () => saveBounds('uptime', uptimeWindow.getBounds()));
    uptimeWindow.on('closed', () => { uptimeWindow = null; });
}

ipcMain.on('open-remote', () => createRemoteWindow());
ipcMain.on('open-timer-window', () => createTimerWindow());
ipcMain.on('open-roulette-window', () => createRouletteWindow());
ipcMain.on('open-uptime-window', (e, { startTime, rouletteId }) => createUptimeWindow(startTime, rouletteId));

ipcMain.on('close-timer-window', () => { if (timerWindow) timerWindow.close(); });
ipcMain.on('close-roulette-window', () => { if (rouletteWindow) rouletteWindow.close(); });
ipcMain.on('close-uptime-window', () => { if (uptimeWindow) uptimeWindow.close(); });

ipcMain.on('connect-tiktok', (event, data) => connectTikTok(data.username));
ipcMain.on('connect-da', (event, credentials) => connectDonationAlertsOAuth(credentials.clientId));
ipcMain.on('connect-dp', (event, apiKey) => connectDonatePay(apiKey));
ipcMain.on('connect-dx', (event, token) => connectDonateX(token));

function disconnectTikTok() {
    if (tiktokConnection) {
        try { 
            tiktokConnection.disconnect(); 
        } catch(e) {}
        tiktokConnection = null;
    }
    if (reconnectTimeout) { clearTimeout(reconnectTimeout); reconnectTimeout = null; }
    
    currentUsername = ''; isConnecting = false; activeTikTokUsername = null;
    currentStreamerInfo = { username: 'Стример', avatar: 'https://cdn-icons-png.flaticon.com/512/1055/1055823.png' };
    
    lastProcessedLikesMilestones = {};
    
    timerState.userLikes = {};
    timerState.subbedUsers.clear();
    currentStreamTotalLikes = 0;
    
    broadcastTime(); 
}

function disconnectDonatePay() {
    if (dpInterval) { clearInterval(dpInterval); dpInterval = null; }
    lastDpDonationId = null; updateDpStatus('Отключено пользователем');
}

function disconnectDonateX() {
    if (dxInterval) { clearInterval(dxInterval); dxInterval = null; }
    updateDxStatus('Отключено пользователем');
}

ipcMain.on('disconnect-tiktok', () => { disconnectTikTok(); updateTtStatus('Отключено пользователем', false); });
ipcMain.on('disconnect-da', () => { clearDaToken(); if (daWs) { daWs.close(); daWs = null; } isDAConnecting = false; updateDaStatus('Отключено пользователем'); });
ipcMain.on('disconnect-dp', disconnectDonatePay);
ipcMain.on('disconnect-dx', disconnectDonateX);

ipcMain.on('update-settings', (event, newConfig) => {
    timerState.settings = newConfig;
    BrowserWindow.getAllWindows().forEach(win => { if (!win.isDestroyed()) win.webContents.send('settings-updated', newConfig); });
});

ipcMain.on('mp-join', (e, { roomId }) => {
    if (!ioClient) return;
    if (mpSocket) { mpSocket.disconnect(); }
    
    mpRoomId = roomId;
    const joinName = currentUsername || timerState.settings?.username || 'Стример';

    mpSocket = ioClient.io('https://servastral-production-ba5f.up.railway.app/', { transports: ['websocket'] });
    
    mpSocket.on('connect', () => {
        mpSocket.emit('join_room', { 
            roomId, 
            username: joinName, 
            isStreamActive: isTtActive,
            avatar: currentStreamerInfo.avatar,
            nickname: currentStreamerInfo.username
        });
        broadcastMpStatus();
    });

    mpSocket.on('room_users_update', (users) => {
        mpUsers = users;
        broadcastMpStatus();
        enrichMpUsers(mpUsers); 
    });

    mpSocket.on('kicked', (reason) => {
        if (mpSocket) mpSocket.disconnect();
        mpRoomId = null;
        mpUsers = [];
        broadcastMpStatus(reason);
    });

    mpSocket.on('action_received', async (data) => {
        if (timerState.isVictory || timerState.isRollingBonus) return;
        const { from, target, actionData } = data;
        
        let attackerName = from || 'Соперник';
        let attackerAvatar = 'https://cdn-icons-png.flaticon.com/512/2952/2952338.png';
        
        const cleanAttacker = (from || '').replace('@', '');
        if (mpUserCache[cleanAttacker]) {
            attackerName = mpUserCache[cleanAttacker].nickname;
            attackerAvatar = mpUserCache[cleanAttacker].avatar;
        } else if (from) {
            const info = await getTikTokProfile(from);
            if (info && (info.nickname || info.avatar)) {
                attackerName = info.nickname || attackerName;
                attackerAvatar = info.avatar || attackerAvatar;
                mpUserCache[cleanAttacker] = { nickname: attackerName, avatar: attackerAvatar };
                saveProfileCache();
            }
        }
        const attackerUser = { username: attackerName, avatar: attackerAvatar, originalUsername: from };

        if (actionData.type === 'swap_time') {
            const myOldTime = timerState.timeLeft;
            const attackerTime = actionData.senderTime || 0;
            
            timerState.timeLeft = attackerTime;
            
            if (timerState.timeLeft <= 0) {
                timerState.timeLeft = 0;
                if (!timerState.settings.bonusEnabled) {
                    timerState.isVictory = true; timerState.isRunning = false;
                } else {
                    timerState.isBonusPhase = true; timerState.isRollingBonus = true; timerState.isRunning = false;
                    const min = timerState.settings.bonusMin || 60; const max = timerState.settings.bonusMax || 300;
                    const bonusTime = Math.floor(Math.random() * (max - min + 1)) + min;
                    const bonusData = { username: attackerName, amount: bonusTime };
                    
                    if (rouletteWindow && !rouletteWindow.isDestroyed()) rouletteWindow.webContents.send('start-bonus-roll', bonusData);
                    else { createRouletteWindow(); setTimeout(() => { if (rouletteWindow && !rouletteWindow.isDestroyed()) rouletteWindow.webContents.send('start-bonus-roll', bonusData); }, 1500); }
                }
            } else { timerState.isVictory = false; timerState.isRunning = true; }

            broadcastTime();
            broadcastAlert({ id: Date.now() + Math.random(), username: attackerName, avatar: attackerAvatar, giftName: `ОБМЕН ТАЙМЕРОМ!`, timeAdded: attackerTime - myOldTime, type: 'special', isSpecial: true, targetTime: timerState.timeLeft });

            if (mpSocket && mpSocket.connected) {
                mpSocket.emit('apply_action', { targetUsername: from, actionData: { type: 'force_set_time', value: myOldTime, label: 'Обмен таймером' } });
            }
            return;
        }

        if (actionData.type === 'force_set_time') {
            const myOldTime = timerState.timeLeft;
            const newTime = actionData.value || 0;
            timerState.timeLeft = newTime;
            
            if (timerState.timeLeft <= 0) {
                timerState.timeLeft = 0;
                if (!timerState.settings.bonusEnabled) {
                    timerState.isVictory = true; timerState.isRunning = false;
                } else {
                    timerState.isBonusPhase = true; timerState.isRollingBonus = true; timerState.isRunning = false;
                    const min = timerState.settings.bonusMin || 60; const max = timerState.settings.bonusMax || 300;
                    const bonusTime = Math.floor(Math.random() * (max - min + 1)) + min;
                    const bonusData = { username: attackerName, amount: bonusTime };
                    
                    if (rouletteWindow && !rouletteWindow.isDestroyed()) rouletteWindow.webContents.send('start-bonus-roll', bonusData);
                    else { createRouletteWindow(); setTimeout(() => { if (rouletteWindow && !rouletteWindow.isDestroyed()) rouletteWindow.webContents.send('start-bonus-roll', bonusData); }, 1500); }
                }
            } else { timerState.isVictory = false; timerState.isRunning = true; }

            broadcastTime();
            broadcastAlert({ id: Date.now() + Math.random(), username: attackerName, avatar: attackerAvatar, giftName: `ТАЙМЕР ОБМЕНЯН!`, timeAdded: newTime - myOldTime, type: 'special', isSpecial: true, targetTime: timerState.timeLeft });
            return;
        }

        executeRouletteWinner(actionData, attackerUser, null, true, attackerName);
        
        setTimeout(() => {
            checkRouletteQueue();
            checkRuinerQueue();
        }, 1000);
    });

    mpSocket.on('disconnect', () => {
        mpRoomId = null;
        mpUsers = [];
        broadcastMpStatus();
    });
});

ipcMain.on('mp-leave', () => {
    if (mpSocket) {
        mpSocket.disconnect();
        mpSocket = null;
    }
    mpRoomId = null;
    mpUsers = [];
    broadcastMpStatus();
});

ipcMain.on('apply-mp-action', (e, { targetUsername, actionData, originalUser }) => {
    if (actionData.type === 'swap_time') {
        actionData.senderTime = timerState.timeLeft;
    }
    if (mpSocket && mpSocket.connected) {
        mpSocket.emit('apply_action', { targetUsername, actionData });
    }
    
    let targetLabel = targetUsername;
    if (targetUsername !== 'all') {
        const targetInfo = mpUsers.find(u => u.username === targetUsername);
        if (targetInfo && targetInfo.nickname) targetLabel = targetInfo.nickname;
    }

    broadcastAlert({ 
        id: Date.now() + Math.random(), 
        username: originalUser.username, 
        avatar: originalUser.avatar, 
        giftName: targetUsername === 'all' ? `АТАКА НА ВСЕХ!` : `АТАКА НА ${targetLabel.toUpperCase()}!`, 
        timeAdded: 0, 
        type: 'special', 
        isSpecial: true,
        targetTime: timerState.timeLeft 
    });
    
    isRouletteBusy = false;
    setTimeout(() => {
        checkRouletteQueue();
        checkRuinerQueue();
    }, 1000);
});

app.whenReady().then(() => {
    createMainWindow();
    
    const savedToken = loadDaToken();
    if (savedToken) {
        updateDaStatus('Автоподключение...');
        establishDaConnection(savedToken);
    }

    setInterval(() => {
        if (timerState.isRunning && !timerState.isVictory && !timerState.isRollingBonus) {
            
            if (timerState.isReversed) {
                timerState.timeLeft += 1;
            } else {
                if (timerState.timeLeft > 0) {
                    timerState.timeLeft -= 1;
                }
            }

            if (timerState.isFrozen && timerState.freezeTimeLeft > 0) {
                timerState.freezeTimeLeft -= 1;
                if (timerState.freezeTimeLeft <= 0) {
                    timerState.isFrozen = false;
                }
            }

            if (ruinerState.isActive) {
                ruinerState.timeLeft -= 1;
                if (ruinerState.timeLeft <= 0) {
                    ruinerState.isActive = false;
                    ruinerState.timeLeft = 0;
                    
                    const min = timerState.settings.ruinerMinTime || 60;
                    const max = timerState.settings.ruinerMaxTime || 300;
                    
                    const ruinerSlots = [];
                    for (let i = 0; i < 15; i++) {
                        const randTime = Math.floor(Math.random() * (max - min + 1)) + min;
                        ruinerSlots.push({
                            id: 'ruiner_slot_' + i,
                            label: `+${randTime} СЕК`,
                            type: 'add_time',
                            value: randTime,
                            chance: 10,
                            color: '#ef4444',
                            isEnabled: true,
                            target: 'self'
                        });
                    }

                    rouletteQueue.push({ 
                        user: { username: ruinerState.user.username, avatar: ruinerState.user.avatar, triggerGift: { name: 'ЗАРУИНЕНО!', icon: 'https://cdn-icons-png.flaticon.com/512/3277/3277450.png' } },
                        slots: ruinerSlots,
                        rouletteId: 'ruiner_timeout'
                    });
                    checkRouletteQueue();
                }
            }
            
            if (timerState.forceVictory) {
                timerState.timeLeft = 0; 
                timerState.isRunning = false; 
                timerState.isVictory = true; 
                timerState.forceVictory = false;
                timerState.isReversed = false;
            } else if (timerState.timeLeft <= 0) {
                timerState.isReversed = false;
                if (timerState.settings.bonusEnabled && !timerState.isBonusPhase) {
                    timerState.timeLeft = 0; timerState.isBonusPhase = true; timerState.isRollingBonus = true; timerState.isRunning = false; 
                    
                    const min = timerState.settings.bonusMin || 60;
                    const max = timerState.settings.bonusMax || 300;
                    const bonusTime = Math.floor(Math.random() * (max - min + 1)) + min;
                    const bonusData = { username: timerState.bonusTriggerUser || 'Зритель', amount: bonusTime };
                    
                    if (rouletteWindow && !rouletteWindow.isDestroyed()) {
                        rouletteWindow.webContents.send('start-bonus-roll', bonusData);
                    } else {
                        createRouletteWindow();
                        setTimeout(() => { if (rouletteWindow && !rouletteWindow.isDestroyed()) rouletteWindow.webContents.send('start-bonus-roll', bonusData); }, 1500);
                    }
                } else {
                    timerState.timeLeft = 0; timerState.isRunning = false; timerState.isVictory = true;
                }
            }

            if (multiplierState.isActive && multiplierState.timeLeft > 0) {
                multiplierState.timeLeft -= 1;
                if (multiplierState.timeLeft <= 0) { multiplierState.isActive = false; multiplierState.value = 1; }
            }
            
            broadcastTime();
        }
    }, 1000);
});

app.on('window-all-closed', () => { if (process.platform !== 'darwin') app.quit(); });

function broadcastTime() {
    const payload = { 
        timeLeft: timerState.timeLeft, isVictory: timerState.isVictory, isRunning: timerState.isRunning,
        multiplier: multiplierState, isBonusPhase: timerState.isBonusPhase, isRollingBonus: timerState.isRollingBonus,
        isFrozen: timerState.isFrozen, freezeTimeLeft: timerState.freezeTimeLeft,
        isReversed: timerState.isReversed, 
        currentTotalLikes: currentStreamTotalLikes,
        ruiner: { 
            ...ruinerState, 
            queueCount: ruinerQueue.length,
            totalSavesNeeded: (ruinerState.isActive ? 1 : 0) + ruinerQueue.length
        }
    };
    if (mainWindow && !mainWindow.isDestroyed()) mainWindow.webContents.send('timer-tick', payload);
    if (remoteWindow && !remoteWindow.isDestroyed()) remoteWindow.webContents.send('timer-tick', payload);
    if (timerWindow && !timerWindow.isDestroyed()) timerWindow.webContents.send('timer-tick', payload);
    if (rouletteWindow && !rouletteWindow.isDestroyed()) rouletteWindow.webContents.send('timer-tick', payload);
    if (uptimeWindow && !uptimeWindow.isDestroyed()) uptimeWindow.webContents.send('timer-tick', payload);
}

function broadcastAlert(alertData) {
    if (timerWindow && !timerWindow.isDestroyed()) timerWindow.webContents.send('new-alert', alertData);
    if (remoteWindow && !remoteWindow.isDestroyed()) remoteWindow.webContents.send('new-alert', alertData);
    if (rouletteWindow && !rouletteWindow.isDestroyed()) rouletteWindow.webContents.send('new-alert', alertData);
}

ipcMain.on('get-initial-status', (e) => {
    e.reply('da-status', daStatusText); 
    e.reply('tiktok-status', { 
        text: ttStatusText, 
        isActive: isTtActive,
        avatar: currentStreamerInfo.avatar,
        nickname: currentStreamerInfo.username
    });
    e.reply('dp-status', dpStatusText); 
    e.reply('dx-status', dxStatusText);
    
    e.reply('mp-status', {
        isConnected: mpSocket && mpSocket.connected,
        roomId: mpRoomId,
        users: mpUsers,
        error: null
    });
});

ipcMain.on('bonus-roll-finished', (e, finalTime) => {
    timerState.timeLeft = finalTime; timerState.isRollingBonus = false; timerState.isRunning = true; broadcastTime();
});

ipcMain.on('start-timer', (event, config) => {
    timerState.settings = config; 
    
    if (timerState.settings.roulettes) {
        timerState.settings.roulettes = timerState.settings.roulettes.map(r => ({
            ...r,
            originalSlots: [...(r.slots || [])]
        }));
    }
    
    timerState.timeLeft = config.initialTime * 60; timerState.isRunning = true;
    multiplierState = { isActive: false, type: 'buff', value: 1, timeLeft: 0 };
    rouletteQueue = []; isRouletteBusy = false; timerState.isBonusPhase = false;
    timerState.isRollingBonus = false; timerState.bonusTriggerUser = ''; timerState.forceVictory = false;
    timerState.isFrozen = false; timerState.freezeTimeLeft = 0;
    timerState.isReversed = false;
    
    ruinerQueue = [];
    isRuinerPaused = false;
    ruinerState = { isActive: false, timeLeft: 0, user: { username: '', avatar: '' } };

    if (timerState.timeLeft <= 0) { timerState.timeLeft = 0; timerState.isVictory = true; timerState.isRunning = false; } 
    else { timerState.isVictory = false; }
    
    timerState.subbedUsers.clear(); timerState.userLikes = {};
    lastProcessedLikesMilestones = {}; 
    
    broadcastTime(); createTimerWindow();
    if (currentUsername !== config.username && config.username) {
        connectTikTok(config.username);
    }
});

ipcMain.on('stop-timer', () => {
    timerState.isRunning = false; rouletteQueue = []; isRouletteBusy = false;
    timerState.isFrozen = false; timerState.freezeTimeLeft = 0; timerState.isReversed = false;
    multiplierState = { isActive: false, type: 'buff', value: 1, timeLeft: 0 }; 
    ruinerQueue = [];
    isRuinerPaused = false;
    ruinerState = { isActive: false, timeLeft: 0, user: { username: '', avatar: '' } };
    broadcastTime();
});

ipcMain.on('manual-add', (e, seconds, sName, sAvatar) => { timerState.timeLeft += seconds; if (timerState.timeLeft > 0) timerState.isVictory = false; broadcastTime(); });
ipcMain.on('manual-sub', (e, seconds, sName, sAvatar) => { 
    timerState.timeLeft -= seconds; 
    if (timerState.timeLeft <= 0) { 
        timerState.timeLeft = 0; 
        timerState.isVictory = true; 
        timerState.isRunning = false; 
        timerState.isReversed = false;
    } 
    broadcastTime(); 
});
ipcMain.on('manual-set', (e, seconds) => { 
    timerState.timeLeft = seconds; 
    if (seconds <= 0) { 
        timerState.timeLeft = 0; 
        timerState.isVictory = true; 
        timerState.isRunning = false; 
        timerState.isReversed = false;
    } else { 
        timerState.isVictory = false; 
    } 
    broadcastTime(); 
});
ipcMain.on('toggle-timer', () => { timerState.isRunning = !timerState.isRunning; broadcastTime(); });

ipcMain.on('manual-freeze', (e, sName, sAvatar) => { 
    timerState.isFrozen = true; 
    timerState.freezeTimeLeft += (timerState.settings.freezeDuration || 60); 
    broadcastTime(); 
});
ipcMain.on('manual-unfreeze', (e, sName, sAvatar) => { 
    if (timerState.isFrozen) {
        timerState.freezeTimeLeft -= (timerState.settings.unfreezeDuration || 60); 
        if (timerState.freezeTimeLeft <= 0) {
            timerState.isFrozen = false;
            timerState.freezeTimeLeft = 0;
        }
        broadcastTime();
    }
});
ipcMain.on('manual-reverse', (e, sName, sAvatar) => {
    timerState.isReversed = !timerState.isReversed;
    broadcastTime();
});

ipcMain.on('manual-ruiner', (e, sName, sAvatar) => {
    ruinerQueue.push({ username: sName || 'Пульт (Руинер)', avatar: sAvatar || 'https://cdn-icons-png.flaticon.com/512/2888/2888661.png' });
    checkRuinerQueue();
});

ipcMain.on('manual-save', (e, sName, sAvatar) => {
    if (ruinerState.isActive || ruinerQueue.length > 0) {
        let savedCount = 0;
        if (ruinerState.isActive) {
            ruinerState.isActive = false;
            ruinerState.timeLeft = 0;
            savedCount++;
        } else if (ruinerQueue.length > 0) {
            ruinerQueue.shift();
            savedCount++;
        }
        if (savedCount > 0) {
            isRuinerPaused = true;
            broadcastAlert({ id: Date.now() + Math.random(), username: sName || 'Пульт (Сейв)', avatar: sAvatar || 'https://cdn-icons-png.flaticon.com/512/2888/2888661.png', giftName: "СЕЙВ!", giftIcon: '', timeAdded: 0, type: 'save', amount: savedCount, targetTime: timerState.timeLeft, isSpecial: true });
            broadcastTime();
            setTimeout(() => {
                isRuinerPaused = false;
                checkRuinerQueue();
            }, 4000);
        }
    }
});

function spinRoulette(queueItem) {
    let slots = queueItem.slots || [];
    if (!slots || slots.length === 0) { isRouletteBusy = false; return; }
    
    let validOpponents = [];
    if (mpSocket && mpSocket.connected) {
        const selfName = currentUsername || timerState.settings?.username || 'Стример';
        validOpponents = mpUsers.filter(u => u.username !== selfName && u.isStreamActive);
    }

    let enabledSlots = slots.filter(slot => slot.isEnabled !== false);
    
    if (validOpponents.length === 0) {
        enabledSlots = enabledSlots.filter(slot => !['opponent', 'all', 'random'].includes(slot.target));
    }

    if (enabledSlots.length === 0) {
        isRouletteBusy = false;
        setTimeout(() => { checkRouletteQueue(); checkRuinerQueue(); }, 500);
        return; 
    }
    
    let availableSlots = enabledSlots;
    
    if (timerState.isFrozen) {
        availableSlots = availableSlots.filter(slot => !['multiplier', 'debuff', 'freeze'].includes(slot.type));
        if (availableSlots.length === 0) availableSlots = enabledSlots;
    } else {
        availableSlots = availableSlots.filter(slot => slot.type !== 'unfreeze');
        if (availableSlots.length === 0) availableSlots = enabledSlots;
    }

    if (timerState.timeLeft <= 300) {
        availableSlots = availableSlots.filter(slot => !['sub_time', 'divide_time'].includes(slot.type));
        if (availableSlots.length === 0) availableSlots = enabledSlots;
    }
    
    if (timerState.timeLeft < 420) {
        availableSlots = availableSlots.filter(slot => slot.type !== 'debuff');
        if (availableSlots.length === 0) availableSlots = enabledSlots;
    }

    if (multiplierState.isActive) {
        availableSlots = availableSlots.filter(slot => !['multiplier', 'debuff'].includes(slot.type));
        if (availableSlots.length === 0) availableSlots = enabledSlots; 
    }
    
    let totalWeight = availableSlots.reduce((sum, slot) => sum + Number(slot.chance), 0);
    if (totalWeight <= 0) totalWeight = 1;
    let random = Math.random() * totalWeight; let winner = null;
    for (let slot of availableSlots) { if (random < slot.chance) { winner = slot; break; } random -= slot.chance; }
    if (!winner) winner = availableSlots[availableSlots.length - 1];

    if (rouletteWindow && !rouletteWindow.isDestroyed()) { 
        rouletteWindow.webContents.send('start-roulette', { winner, slots: availableSlots, user: queueItem.user, rouletteId: queueItem.rouletteId }); 
    } 
    else {
        createRouletteWindow();
        setTimeout(() => { if (rouletteWindow && !rouletteWindow.isDestroyed()) rouletteWindow.webContents.send('start-roulette', { winner, slots: availableSlots, user: queueItem.user, rouletteId: queueItem.rouletteId }); }, 1500);
    }
}

function checkRouletteQueue() {
    if (isRouletteBusy || rouletteQueue.length === 0 || timerState.isVictory) return;
    isRouletteBusy = true; const nextItem = rouletteQueue.shift(); spinRoulette(nextItem);
}

function checkRuinerQueue() {
    if (ruinerState.isActive || ruinerQueue.length === 0 || timerState.isVictory || isRouletteBusy || isRuinerPaused) return;
    const nextRuiner = ruinerQueue.shift();
    ruinerState.isActive = true;
    ruinerState.timeLeft = timerState.settings.ruinerDuration || 60;
    ruinerState.user = { username: nextRuiner.username, avatar: nextRuiner.avatar };
    broadcastAlert({ id: Date.now() + Math.random(), username: nextRuiner.username, avatar: nextRuiner.avatar, giftName: "РУИНЕР ЗАПУЩЕН!", giftIcon: '', timeAdded: 0, type: 'ruiner', amount: 1, targetTime: timerState.timeLeft });
    broadcastTime();
}

ipcMain.on('manual-trigger-roulette', (e, rouletteId, sName, sAvatar) => {
    let targetRoulette = null;
    if (timerState.settings.roulettes && timerState.settings.roulettes.length > 0) {
        targetRoulette = rouletteId 
            ? timerState.settings.roulettes.find(r => r.id === rouletteId) 
            : timerState.settings.roulettes[0];
    }
    
    if (!targetRoulette) return;

    rouletteQueue.push({ 
        user: { username: sName || currentStreamerInfo.username || 'Стример', avatar: sAvatar || currentStreamerInfo.avatar || 'https://cdn-icons-png.flaticon.com/512/2888/2888661.png', triggerGift: { name: 'Запуск с Пульта', icon: 'https://cdn-icons-png.flaticon.com/512/2888/2888661.png' } },
        slots: targetRoulette.slots,
        rouletteId: targetRoulette.id
    });
    checkRouletteQueue();
});

function executeRouletteWinner(winner, user, rouletteId, isMpReceived = false, attackerName = '') {
    let addedTime = 0; let alertTimeAdded = 0; let isSpecial = false; let alertText = winner.label;
    
    if (winner.isEliminable && rouletteId && !isMpReceived) {
        if (timerState.settings.roulettes) {
            const rIndex = timerState.settings.roulettes.findIndex(r => r.id === rouletteId);
            if (rIndex !== -1) {
                let updatedSlots = timerState.settings.roulettes[rIndex].slots.filter(s => s.id !== winner.id);
                if (updatedSlots.length === 0) { 
                    updatedSlots = [...(timerState.settings.roulettes[rIndex].originalSlots || [])]; 
                }
                timerState.settings.roulettes[rIndex].slots = updatedSlots;
                BrowserWindow.getAllWindows().forEach(win => { if (!win.isDestroyed()) win.webContents.send('settings-updated', timerState.settings); });
            }
        }
    }

    if (winner.type === 'set_time') {
        let oldTime = timerState.timeLeft; timerState.timeLeft = winner.value; addedTime = timerState.timeLeft - oldTime;
    } else if (winner.type === 'reset_time') {
        let oldTime = timerState.timeLeft; timerState.timeLeft = 0; timerState.forceVictory = true; addedTime = -oldTime;
    } else if (winner.type === 'swap_time') {
        alertText = `ОБМЕН (НЕТ СОПЕРНИКА)`;
        isSpecial = true;
        addedTime = 0;
    } else if (winner.type === 'freeze') {
        timerState.isFrozen = true; 
        timerState.freezeTimeLeft += (timerState.settings.freezeDuration || 60); 
        alertText = '❄️ ЗАМОРОЗКА!';
        isSpecial = true;
    } else if (winner.type === 'unfreeze') {
        if (timerState.isFrozen) {
            timerState.freezeTimeLeft -= (timerState.settings.unfreezeDuration || 60);
            if (timerState.freezeTimeLeft <= 0) {
                timerState.isFrozen = false;
                timerState.freezeTimeLeft = 0;
            }
        }
        alertText = '🔥 РАЗМОРОЗКА!';
        isSpecial = true;
    } else if (winner.type === 'reverse_time') {
        timerState.isReversed = !timerState.isReversed;
        alertText = timerState.isReversed ? 'ВРЕМЯ ВСПЯТЬ!' : 'ВРЕМЯ ВПЕРЕД!';
        isSpecial = true;
    } else if (winner.type === 'extra_spin') {
        let spinsCount = winner.value || 1;
        alertText = `ЕЩЕ ПРОКРУТ (x${spinsCount})`;
        isSpecial = true;
        
        let targetSlots = [];
        let targetRouletteId = rouletteId;

        if (timerState.settings.roulettes && timerState.settings.roulettes.length > 0) {
            if (isMpReceived) {
                let mainRoulette = timerState.settings.roulettes.find(r => r.isMain);
                if (!mainRoulette) mainRoulette = timerState.settings.roulettes[0];
                targetSlots = mainRoulette.slots;
                targetRouletteId = mainRoulette.id;
            } else {
                const r = timerState.settings.roulettes.find(r => r.id === rouletteId);
                if (r) targetSlots = r.slots;
                else targetSlots = timerState.settings.roulettes[0].slots;
            }
        }

        for (let i = 0; i < spinsCount; i++) {
            rouletteQueue.unshift({ 
                user: { 
                    username: isMpReceived ? `от ${attackerName}` : user.username, 
                    avatar: user.avatar, 
                    triggerGift: { name: 'Доп. прокрут', icon: 'https://cdn-icons-png.flaticon.com/512/808/808271.png' } 
                },
                slots: targetSlots,
                rouletteId: targetRouletteId
            });
        }
    } else if (winner.type === 'ruiner') {
        let ruinerCount = winner.value || 1;
        alertText = `РУИНЕР (x${ruinerCount})`;
        isSpecial = true;
        for(let i = 0; i < ruinerCount; i++) {
            ruinerQueue.push({ username: isMpReceived ? attackerName : user.username, avatar: user.avatar });
        }
        checkRuinerQueue();
        addedTime = 0;
    } else if (winner.type === 'save') {
        let saveCount = winner.value || 1;
        let actualSaved = 0;
        for (let i = 0; i < saveCount; i++) {
            if (ruinerState.isActive) { ruinerState.isActive = false; ruinerState.timeLeft = 0; actualSaved++; } 
            else if (ruinerQueue.length > 0) { ruinerQueue.shift(); actualSaved++; }
        }
        if (actualSaved > 0) {
            alertText = `СЕЙВ (x${actualSaved})`;
            isRuinerPaused = true;
            setTimeout(() => { isRuinerPaused = false; checkRuinerQueue(); }, 4000);
        } else {
            alertText = 'СЕЙВ (впустую)';
        }
        isSpecial = true;
        addedTime = 0;
    } else if (winner.type === 'multiplier' || winner.type === 'debuff') {
        let isDebuff = winner.type === 'debuff';
        if (multiplierState.isActive && multiplierState.type === (isDebuff ? 'debuff' : 'buff')) {
            multiplierState.timeLeft += (winner.value || 60); multiplierState.value = winner.multiplierValue || 2;
        } else {
            multiplierState.isActive = true; multiplierState.type = isDebuff ? 'debuff' : 'buff'; multiplierState.value = winner.multiplierValue || 2; multiplierState.timeLeft = winner.value || 60;
        }
        addedTime = 0;
    } else if (winner.type === 'multiply_time') {
        let factor = winner.multiplierValue || 2; let oldTime = timerState.timeLeft; timerState.timeLeft = Math.floor(timerState.timeLeft * factor);
        addedTime = timerState.timeLeft - oldTime; alertTimeAdded = addedTime; alertText = `Время x${factor}`;
    } else if (winner.type === 'divide_time') {
        let factor = winner.multiplierValue || 2; if (factor < 1) factor = 1;
        let oldTime = timerState.timeLeft; let newTime = Math.floor(timerState.timeLeft / factor);
        
        if (oldTime > 300 && newTime < 300) newTime = 300;
        if (oldTime <= 300) newTime = oldTime; 
        
        timerState.timeLeft = newTime; addedTime = timerState.timeLeft - oldTime; alertTimeAdded = addedTime; alertText = `Время /${factor}`;
    } else if (winner.type === 'special') { isSpecial = true; alertText = winner.textValue || winner.label; addedTime = 0; } 
    else {
        let oldTime = timerState.timeLeft;
        if (winner.type === 'add_time') { addedTime = winner.value; timerState.timeLeft += addedTime; }
        if (winner.type === 'sub_time') {
            let timeToSub = Math.abs(winner.value); let newTime = oldTime - timeToSub;
            
            if (oldTime > 300 && newTime < 300) newTime = 300;
            if (oldTime <= 300) newTime = oldTime; 
            
            addedTime = newTime - oldTime; timerState.timeLeft = newTime;
        }
        alertTimeAdded = addedTime;
    }
    
    if (timerState.forceVictory) {
        timerState.timeLeft = 0; timerState.isVictory = true; timerState.isRunning = false; timerState.forceVictory = false; timerState.isReversed = false;
    } else if (timerState.timeLeft <= 0 && !timerState.settings.bonusEnabled) { 
        timerState.timeLeft = 0; timerState.isVictory = true; timerState.isRunning = false; timerState.isReversed = false;
    } 
    else { 
        if (addedTime > 0) timerState.isVictory = false; 
    }

    if (isMpReceived) {
        alertText = `ОТ ${attackerName.toUpperCase()}: ${alertText}`;
        isSpecial = true;
    }

    broadcastAlert({ id: Date.now() + Math.random(), username: user.username, avatar: user.avatar, giftName: alertText, timeAdded: alertTimeAdded, type: 'roulette', isSpecial: isSpecial, targetTime: timerState.timeLeft, isFromRemote: user.triggerGift?.name === 'Запуск с Пульта' });
    requestBroadcastTime(); 
}

ipcMain.on('apply-roulette-result', (e, payload) => {
    if (timerState.isVictory) return; 
    
    const { winner, user, rouletteId } = payload;
    
    if (['opponent', 'all', 'random'].includes(winner.target)) {
        const selfName = currentUsername || timerState.settings?.username || 'Стример';
        const validTargets = mpSocket && mpSocket.connected ? mpUsers.filter(u => u.username !== selfName && u.isStreamActive) : [];
        
        if (winner.type === 'swap_time') {
            winner.senderTime = timerState.timeLeft;
        }

        if (winner.target === 'all') {
            if (validTargets.length > 0) {
                if (mpSocket && mpSocket.connected) {
                    mpSocket.emit('apply_action', { targetUsername: 'all', actionData: winner });
                }
                broadcastAlert({ id: Date.now() + Math.random(), username: user.username, avatar: user.avatar, giftName: `АТАКА НА ВСЕХ!`, timeAdded: 0, type: 'special', isSpecial: true, targetTime: timerState.timeLeft, isFromRemote: user.triggerGift?.name === 'Запуск с Пульта' });
            } else {
                broadcastAlert({ id: Date.now() + Math.random(), username: user.username, avatar: user.avatar, giftName: "Нет соперников (Скип)", timeAdded: 0, type: 'special', isSpecial: true, targetTime: timerState.timeLeft, isFromRemote: user.triggerGift?.name === 'Запуск с Пульта' });
            }
            isRouletteBusy = false;
            setTimeout(() => { checkRouletteQueue(); checkRuinerQueue(); }, 1000);
            return;
        }

        if (validTargets.length === 1) {
            const targetUser = validTargets[0];
            if (mpSocket && mpSocket.connected) {
                mpSocket.emit('apply_action', { targetUsername: targetUser.username, actionData: winner });
            }
            
            const targetLabel = targetUser.nickname || targetUser.username;
            broadcastAlert({ id: Date.now() + Math.random(), username: user.username, avatar: user.avatar, giftName: `АТАКА НА ${targetLabel.toUpperCase()}!`, timeAdded: 0, type: 'special', isSpecial: true, targetTime: timerState.timeLeft, isFromRemote: user.triggerGift?.name === 'Запуск с Пульта' });
            
            isRouletteBusy = false;
            setTimeout(() => { checkRouletteQueue(); checkRuinerQueue(); }, 1000);
            return; 
        } else if (validTargets.length > 1) {
            if (rouletteWindow && !rouletteWindow.isDestroyed()) {
                rouletteWindow.webContents.send('start-user-spin', { users: validTargets, actionData: winner, originalUser: user, includeAll: winner.target === 'random' });
            } else {
                createRouletteWindow();
                setTimeout(() => {
                    if (rouletteWindow && !rouletteWindow.isDestroyed()) {
                        rouletteWindow.webContents.send('start-user-spin', { users: validTargets, actionData: winner, originalUser: user, includeAll: winner.target === 'random' });
                    }
                }, 1500);
            }
            return;
        } else {
            broadcastAlert({ id: Date.now() + Math.random(), username: user.username, avatar: user.avatar, giftName: "Нет соперников (Скип)", timeAdded: 0, type: 'special', isSpecial: true, targetTime: timerState.timeLeft, isFromRemote: user.triggerGift?.name === 'Запуск с Пульта' });
            isRouletteBusy = false;
            setTimeout(() => { checkRouletteQueue(); checkRuinerQueue(); }, 1000);
            return;
        }
    }

    executeRouletteWinner(winner, user, rouletteId, false);
});

ipcMain.on('roulette-animation-finished', () => { 
    isRouletteBusy = false; 
    setTimeout(() => {
        checkRouletteQueue();
        checkRuinerQueue();
    }, 1000); 
});

function addTime(amount, username, ignoreMultiplier = false) {
    if (timerState.isVictory) return 0;
    if (timerState.isFrozen && !ignoreMultiplier) return 0;

    let timeChange = amount;
    
    if (multiplierState.isActive && !ignoreMultiplier) {
        if (multiplierState.type === 'buff') { timeChange = amount > 0 ? amount * multiplierState.value : amount; } 
        else if (multiplierState.type === 'debuff') { timeChange = -Math.abs(amount * multiplierState.value); }
    }
    
    let oldTime = timerState.timeLeft; 
    timerState.timeLeft += timeChange;
    
    if (timerState.timeLeft <= 0) {
        timerState.timeLeft = 0;
        timerState.isReversed = false; 
        if (oldTime > 0) timerState.bonusTriggerUser = username;
    }
    
    return timerState.timeLeft - oldTime;
}

function processTriggerEvent(data) {
    if (timerState.isVictory || timerState.isRollingBonus) return;
    const { isGift, giftIdStr, donationAmount, count, totalCoins, nickname, avatar, giftName, giftIcon } = data;

    let addedTime = 0;
    let eventType = isGift ? 'gift' : 'donation';
    let isSpecial = false;

    if (timerState.isFrozen && isMatched(timerState.settings.isFreezeEnabled, timerState.settings.giftUnfreezeIds, timerState.settings.unfreezeDonationAmount, giftIdStr, donationAmount)) {
        let unfreezeVal = (timerState.settings.unfreezeDuration || 60) * count;
        timerState.freezeTimeLeft -= unfreezeVal;
        if (timerState.freezeTimeLeft <= 0) {
            timerState.isFrozen = false; 
            timerState.freezeTimeLeft = 0;
        }
        broadcastAlert({ id: Date.now() + Math.random(), username: nickname, avatar: avatar, giftName: giftName, giftIcon: giftIcon, timeAdded: 0, type: 'unfreeze', amount: count, targetTime: timerState.timeLeft });
        requestBroadcastTime(); 
        return;
    }

    if ((ruinerState.isActive || ruinerQueue.length > 0) && isMatched(timerState.settings.isRuinerEnabled, timerState.settings.giftSaveIds, timerState.settings.saveDonationAmount, giftIdStr, donationAmount)) {
        let savedCount = 0;
        for (let i = 0; i < count; i++) {
            if (ruinerState.isActive) {
                ruinerState.isActive = false;
                ruinerState.timeLeft = 0;
                savedCount++;
            } else if (ruinerQueue.length > 0) {
                ruinerQueue.shift();
                savedCount++;
            }
        }
        
        if (savedCount > 0) {
            isRuinerPaused = true;
            broadcastAlert({ id: Date.now() + Math.random(), username: nickname, avatar: avatar, giftName: "СЕЙВ!", giftIcon: giftIcon, timeAdded: 0, type: 'save', amount: savedCount, targetTime: timerState.timeLeft, isSpecial: true });
            requestBroadcastTime(); 
            
            setTimeout(() => {
                isRuinerPaused = false;
                checkRuinerQueue();
            }, 4000);
        }
        return;
    }

    if (isMatched(timerState.settings.isRuinerEnabled, timerState.settings.giftRuinerIds, timerState.settings.ruinerDonationAmount, giftIdStr, donationAmount)) {
        for (let i = 0; i < count; i++) {
            ruinerQueue.push({ username: nickname, avatar: avatar });
        }
        checkRuinerQueue();
        return;
    }

    let isRouletteTriggered = false;
    if (timerState.settings.roulettes && timerState.settings.roulettes.length > 0) {
        timerState.settings.roulettes.forEach(roulette => {
            if (roulette.triggerType === 'gift' || roulette.triggerType === 'both') {
                if (isMatched(true, roulette.triggerGiftIds, roulette.donationAmount, giftIdStr, donationAmount)) {
                    isRouletteTriggered = true;
                    for(let i=0; i<count; i++) { 
                        rouletteQueue.push({ 
                            user: { username: nickname, avatar: avatar, triggerGift: { name: giftName, icon: giftIcon } },
                            slots: roulette.slots,
                            rouletteId: roulette.id
                        }); 
                    }
                    
                    let costToAdd = isGift ? totalCoins : Math.floor(donationAmount || 0);

                    if (roulette.addsCost && costToAdd > 0 && !timerState.isFrozen) {
                        let timeAdded = addTime(costToAdd, nickname, true);
                        broadcastAlert({ id: Date.now() + Math.random(), username: nickname, avatar: avatar, giftName: giftName, giftIcon: giftIcon, timeAdded: timeAdded, type: 'roulette', amount: count, targetTime: timerState.timeLeft });
                    } else {
                        broadcastAlert({ id: Date.now() + Math.random(), username: nickname, avatar: avatar, giftName: giftName, giftIcon: giftIcon, timeAdded: 0, type: 'roulette', amount: count, targetTime: timerState.timeLeft });
                    }
                }
            }
        });
    }

    if (isRouletteTriggered) {
        requestBroadcastTime(); 
        checkRouletteQueue();
        return; 
    }

    if (isMatched(timerState.settings.isFreezeEnabled, timerState.settings.giftFreezeIds, timerState.settings.freezeDonationAmount, giftIdStr, donationAmount)) {
        timerState.isFrozen = true; 
        timerState.freezeTimeLeft += (timerState.settings.freezeDuration || 60) * count;
        broadcastAlert({ id: Date.now() + Math.random(), username: nickname, avatar: avatar, giftName: giftName, giftIcon: giftIcon, timeAdded: 0, type: 'freeze', amount: count, targetTime: timerState.timeLeft });
        requestBroadcastTime(); 
        return;
    }
    
    if (isMatched(timerState.settings.isReverseEnabled, timerState.settings.giftReverseIds, timerState.settings.reverseDonationAmount, giftIdStr, donationAmount)) {
        timerState.isReversed = !timerState.isReversed;
        broadcastAlert({ id: Date.now() + Math.random(), username: nickname, avatar: avatar, giftName: giftName, giftIcon: giftIcon, timeAdded: 0, type: 'reverse_time', amount: count, targetTime: timerState.timeLeft });
        requestBroadcastTime(); 
        return;
    }

    if (timerState.isFrozen) {
        broadcastAlert({ id: Date.now() + Math.random(), username: nickname, avatar: avatar, giftName: giftName, giftIcon: giftIcon, timeAdded: 0, type: 'frozen_gift', amount: count, targetTime: timerState.timeLeft });
        return;
    }

    if (isMatched(timerState.settings.isMultiplierGiftEnabled, timerState.settings.giftMultiplierIds, timerState.settings.multiplierDonationAmount, giftIdStr, donationAmount)) {
        let durationToAdd = (timerState.settings.multiplierDuration || 60) * count;
        if (multiplierState.isActive && multiplierState.type === 'buff') { 
            multiplierState.timeLeft += durationToAdd; multiplierState.value = timerState.settings.multiplierValue || 2; 
        } else { 
            multiplierState.isActive = true; multiplierState.type = 'buff'; multiplierState.value = timerState.settings.multiplierValue || 2; multiplierState.timeLeft = durationToAdd; 
        }
        broadcastAlert({ id: Date.now() + Math.random(), username: nickname, avatar: avatar, giftName: giftName, giftIcon: giftIcon, timeAdded: 0, type: 'multiplier', amount: count, targetTime: timerState.timeLeft });
        requestBroadcastTime(); 
        return; 
    }

    if (isMatched(timerState.settings.isDebuffGiftEnabled, timerState.settings.giftDebuffIds, timerState.settings.debuffDonationAmount, giftIdStr, donationAmount)) {
        let durationToAdd = (timerState.settings.debuffDuration || 60) * count;
        if (multiplierState.isActive && multiplierState.type === 'debuff') { 
            multiplierState.timeLeft += durationToAdd; multiplierState.value = timerState.settings.debuffValue || 2; 
        } else { 
            multiplierState.isActive = true; multiplierState.type = 'debuff'; multiplierState.value = timerState.settings.debuffValue || 2; multiplierState.timeLeft = durationToAdd; 
        }
        broadcastAlert({ id: Date.now() + Math.random(), username: nickname, avatar: avatar, giftName: giftName, giftIcon: giftIcon, timeAdded: 0, type: 'debuff', amount: count, targetTime: timerState.timeLeft });
        requestBroadcastTime(); 
        return; 
    }

    let penaltyTriggered = false;
    if (timerState.settings.penalties && timerState.settings.penalties.length > 0) {
        const pRule = timerState.settings.penalties.find(p => isMatched(p.isEnabled, p.ids, p.donationAmount, giftIdStr, donationAmount));
        if (pRule) {
            eventType = 'penalty';
            penaltyTriggered = true;
            let mult = multiplierState.isActive ? multiplierState.value : 1; 
            let basePenalty = (pRule.penaltyAmount || 600); 
            let threshold = (pRule.penaltyThreshold || 300); 
            let timeToSubtract = basePenalty * mult; 
            for (let i = 0; i < count; i++) {
                if (timerState.timeLeft > threshold) {
                    let diff = timerState.timeLeft - timeToSubtract; 
                    if (diff < threshold) diff = threshold; 
                    addedTime -= (timerState.timeLeft - diff); 
                    timerState.timeLeft = diff;
                }
            }
        }
    } else if (isMatched(timerState.settings.isPenaltyEnabled, timerState.settings.giftPenaltyIds, timerState.settings.penaltyDonationAmount, giftIdStr, donationAmount)) {
        eventType = 'penalty';
        penaltyTriggered = true;
        let mult = multiplierState.isActive ? multiplierState.value : 1; 
        let basePenalty = (timerState.settings.penaltyAmount || 600); 
        let threshold = (timerState.settings.penaltyThreshold || 300); 
        let timeToSubtract = basePenalty * mult; 
        for (let i = 0; i < count; i++) {
            if (timerState.timeLeft > threshold) {
                let diff = timerState.timeLeft - timeToSubtract; 
                if (diff < threshold) diff = threshold; 
                addedTime -= (timerState.timeLeft - diff); 
                timerState.timeLeft = diff;
            }
        }
    }

    if (!penaltyTriggered) {
        if (isMatched(timerState.settings.isSetTimeEnabled, timerState.settings.giftSetTimeIds, timerState.settings.setTimeDonationAmount, giftIdStr, donationAmount)) {
            eventType = 'set_time';
            let targetTime = timerState.settings.setTimeValue || 300; 
            addedTime = targetTime - timerState.timeLeft; 
            timerState.timeLeft = targetTime;
            if (timerState.timeLeft > 0) { timerState.isVictory = false; if (!timerState.isBonusPhase && !timerState.isRollingBonus) timerState.isRunning = true; }
        } 
        else if (isMatched(timerState.settings.isResetEnabled, timerState.settings.giftResetIds, timerState.settings.resetDonationAmount, giftIdStr, donationAmount)) {
            eventType = 'reset_time';
            addedTime = -timerState.timeLeft; 
            timerState.timeLeft = 0; 
            timerState.forceVictory = true; 
            timerState.isVictory = true;
            timerState.isRunning = false;
            timerState.isReversed = false;
        } 
        else {
            const customRule = timerState.settings.customTriggers?.find(rule => isMatched(rule.isEnabled, rule.ids, rule.donationAmount, giftIdStr, donationAmount));
            if (customRule) {
                eventType = customRule.type;
                if (customRule.type === 'add') { 
                    addedTime = addTime((customRule.value || 0) * count, nickname); 
                } else if (customRule.type === 'sub') { 
                    addedTime = addTime(-Math.abs(customRule.value || 0) * count, nickname); 
                } else if (customRule.type === 'set') { 
                    let targetTime = customRule.value || 0; 
                    addedTime = targetTime - timerState.timeLeft; 
                    timerState.timeLeft = targetTime; 
                    if (timerState.timeLeft > 0) { 
                        timerState.isVictory = false; 
                        if (!timerState.isBonusPhase && !timerState.isRollingBonus) timerState.isRunning = true; 
                    }
                } else if (customRule.type === 'reset') { 
                    addedTime = -timerState.timeLeft; 
                    timerState.timeLeft = 0; 
                    timerState.forceVictory = true; 
                    timerState.isVictory = true;
                    timerState.isRunning = false;
                    timerState.isReversed = false;
                }
            } else { 
                let costToAdd = isGift ? totalCoins : Math.floor(donationAmount || 0);
                addedTime = addTime(costToAdd, nickname); 
            }
        }
    }

    let costToAlert = isGift ? totalCoins : Math.floor(donationAmount || 0);
    if (addedTime !== 0 || costToAlert > 0 || ['set_time', 'reset_time', 'set', 'reset', 'penalty'].includes(eventType)) { 
        broadcastAlert({ id: Date.now() + Math.random(), username: nickname, avatar: avatar, giftName: giftName, giftIcon: giftIcon, timeAdded: addedTime, type: eventType, amount: count, targetTime: timerState.timeLeft }); 
    }
    requestBroadcastTime(); 
}

function processGenericDonation(id, username, amount, currency, platform) {
    if (timerState.isVictory || timerState.isRollingBonus) return; 
    const rawAmount = parseFloat(amount); if (isNaN(rawAmount) || rawAmount <= 0) return;

    const exchangeRates = { 'USD': 92, 'EUR': 100, 'KZT': 0.2, 'BYN': 28, 'UAH': 2.4, 'RUB': 1 };
    const curr = String(currency || 'RUB').toUpperCase();
    let amountInRub = rawAmount * (exchangeRates[curr] || 1);
    let roundedRub = Math.round(amountInRub); 

    updateTopDonators(username || 'Аноним', 'https://cdn-icons-png.flaticon.com/512/5272/5272370.png', roundedRub);

    processTriggerEvent({
        isGift: false,
        giftIdStr: null,
        donationAmount: roundedRub,
        count: 1,
        totalCoins: 0,
        nickname: username || 'Аноним',
        avatar: 'https://cdn-icons-png.flaticon.com/512/5272/5272370.png',
        giftName: `Донат ${rawAmount} ${curr}`,
        giftIcon: 'https://cdn-icons-png.flaticon.com/512/5272/5272370.png'
    });
}

async function connectDonatePay(apiKey) {
    if (!apiKey) return;
    disconnectDonatePay(); updateDpStatus('Подключение...');
    try {
        const params = new URLSearchParams();
        params.append('access_token', apiKey); params.append('limit', '1');
        params.append('type', 'donation'); params.append('status', 'success');

        const res = await net.fetch('https://donatepay.ru/api/v1/transactions', {
            method: 'POST', headers: { 'Content-Type': 'application/x-www-form-urlencoded', 'User-Agent': 'Marfaley/2.0' },
            body: params.toString()
        });
        const data = await res.json();
        
        if (data.status === 'success') {
            updateDpStatus('Успешно подключено');
            if (data.data && data.data.length > 0) lastDpDonationId = data.data[0].id;
            dpInterval = setInterval(() => pollDonatePay(apiKey), 10000);
            if (mainWindow && !mainWindow.isDestroyed()) mainWindow.webContents.send('play-success-sound');
        } else { throw new Error(data.message || 'Неверный API ключ или настройки доната'); }
    } catch (e) {
        updateDpStatus(`Ошибка: ${e.message}`);
        if (mainWindow && !mainWindow.isDestroyed()) mainWindow.webContents.send('play-error-sound');
    }
}

async function pollDonatePay(apiKey) {
    try {
        const params = new URLSearchParams();
        params.append('access_token', apiKey); params.append('limit', '10');
        params.append('type', 'donation'); params.append('status', 'success');

        const res = await net.fetch('https://donatepay.ru/api/v1/transactions', {
            method: 'POST', headers: { 'Content-Type': 'application/x-www-form-urlencoded', 'User-Agent': 'Marfaley/2.0' },
            body: params.toString()
        });
        const data = await res.json();
        
        if (data.status === 'success' && data.data) {
            const donations = data.data.reverse(); 
            for (let don of donations) {
                if (!lastDpDonationId || don.id > lastDpDonationId) {
                    lastDpDonationId = don.id;
                    processGenericDonation(don.id, don.what || don.name || 'Аноним', don.sum, don.currency, 'DonatePay');
                }
            }
        }
    } catch (e) {}
}

async function connectDonateX(token) {
    if (!token) return;
    disconnectDonateX(); updateDxStatus('Подключение...');
    try {
        const res = await net.fetch(`https://donatex.gg/api/v1/donations?skip=0&take=20`, { headers: { 'Authorization': `Bearer ${token}` } });
        if (res.ok) {
            const data = await res.json();
            updateDxStatus('Успешно подключено');
            if (Array.isArray(data)) { data.forEach(don => dxProcessedIds.add(don.id)); }
            
            dxInterval = setInterval(() => pollDonateX(token), 10000);
            if (mainWindow && !mainWindow.isDestroyed()) mainWindow.webContents.send('play-success-sound');
        } else { throw new Error('Неверный External Token или ошибка доступа'); }
    } catch (e) {
        updateDxStatus(`Ошибка: ${e.message}`);
        if (mainWindow && !mainWindow.isDestroyed()) mainWindow.webContents.send('play-error-sound');
    }
}

async function pollDonateX(token) {
    try {
        const res = await net.fetch(`https://donatex.gg/api/v1/donations?skip=0&take=10`, { headers: { 'Authorization': `Bearer ${token}` } });
        if (res.ok) {
            const data = await res.json();
            if (Array.isArray(data)) {
                const donations = data.reverse();
                for (let don of donations) {
                    if (!dxProcessedIds.has(don.id)) {
                        dxProcessedIds.add(don.id);
                        if(dxProcessedIds.size > 1000) { dxProcessedIds = new Set(Array.from(dxProcessedIds).slice(-100)); }
                        const finalAmount = don.amountInRub || don.amount;
                        processGenericDonation(don.id, don.username || 'Аноним', finalAmount, 'RUB', 'DonateX');
                    }
                }
            }
        }
    } catch (e) {}
}

async function connectDonationAlertsOAuth(clientId) {
    if (!clientId || isDAConnecting) return;
    const cleanClientId = clientId.trim(); isDAConnecting = true;
    if (daWs) { daWs.close(); daWs = null; } updateDaStatus('Ожидание авторизации в окне...');

    try {
        const redirectUri = 'http://localhost/da-callback';
        const authUrl = `https://www.donationalerts.com/oauth/authorize?client_id=${cleanClientId}&response_type=token&scope=oauth-user-show%20oauth-donation-subscribe&redirect_uri=${redirectUri}`;

        let authWindow = new BrowserWindow({
            width: 500, height: 700, show: true, autoHideMenuBar: true, title: "Авторизация DonationAlerts",
            webPreferences: { nodeIntegration: false, contextIsolation: true }
        });
        authWindow.loadURL(authUrl);

        authWindow.webContents.on('will-redirect', async (event, url) => {
            if (url.startsWith(redirectUri)) {
                event.preventDefault(); authWindow.hide(); 
                const hashParams = new URLSearchParams(url.split('#')[1]);
                const accessToken = hashParams.get('access_token');
                if (accessToken) {
                    updateDaStatus('Токен получен. Соединение с сокетом...'); saveDaToken(accessToken); authWindow.close(); await establishDaConnection(accessToken); 
                } else {
                    updateDaStatus('Ошибка: Доступ не предоставлен'); authWindow.close(); isDAConnecting = false;
                }
            }
        });
        authWindow.on('closed', () => { if (isDAConnecting && !daWs) { isDAConnecting = false; updateDaStatus('Авторизация отменена пользователем'); } });
    } catch (err) {
        isDAConnecting = false; updateDaStatus(`Ошибка: ${err.message}`);
        if (mainWindow && !mainWindow.isDestroyed()) mainWindow.webContents.send('play-error-sound');
    }
}

async function establishDaConnection(accessToken) {
    try {
        const res = await net.fetch('https://www.donationalerts.com/api/v1/user/oauth', { headers: { 'Authorization': `Bearer ${accessToken}` } });
        if (!res.ok) { clearDaToken(); throw new Error('Токен устарел или неверный, авторизуйтесь заново'); }
        const userData = await res.json();
        const userId = userData.data.id; const socketToken = userData.data.socket_connection_token;

        daWs = new WebSocket('wss://centrifugo.donationalerts.com/connection/websocket');
        daWs.on('open', () => {
            isDAConnecting = false; daWs.send(JSON.stringify({ "params": { "token": socketToken }, "id": 1 }));
            updateDaStatus('Успешно подключено (Official API)');
            if (mainWindow && !mainWindow.isDestroyed()) mainWindow.webContents.send('play-success-sound');
        });

        daWs.on('message', async (data) => {
            const msg = JSON.parse(data);
            if (msg.id === 1 && msg.result && msg.result.client) {
                const clientId = msg.result.client;
                try {
                    const subRes = await net.fetch('https://www.donationalerts.com/api/v1/centrifuge/subscribe', {
                        method: 'POST', headers: { 'Authorization': `Bearer ${accessToken}`, 'Content-Type': 'application/json' },
                        body: JSON.stringify({ channels: [`$alerts:donation_${userId}`], client: clientId })
                    });
                    if (!subRes.ok) throw new Error('Не удалось подписаться на донаты');
                    const subData = await subRes.json(); const channelToken = subData.channels[0].token;
                    daWs.send(JSON.stringify({ "params": { "channel": `$alerts:donation_${userId}`, "token": channelToken }, "method": 1, "id": 2 }));
                } catch (err) { updateDaStatus(`Ошибка подписки: ${err.message}`); }
            }
            
            let result = msg.result || msg;
            if (result && result.channel === `$alerts:donation_${userId}`) {
                if (result.type === 1 || (result.data && result.data.info)) return;
                let payloadData = result.data;
                if (payloadData && payloadData.data) {
                    try {
                        let donation = typeof payloadData.data === 'string' ? JSON.parse(payloadData.data) : payloadData.data;
                        if (!donation.amount && donation.data && donation.data.amount) { donation = donation.data; }
                        if (donation.amount) {
                            if (timerState.isVictory || timerState.isRollingBonus) return; 
                            let amountInRub = parseFloat(donation.amount_in_user_currency);
                            if (isNaN(amountInRub) || amountInRub <= 0) {
                                const rawAmount = parseFloat(donation.amount); const currency = String(donation.currency || 'RUB').toUpperCase();
                                const exchangeRates = { 'USD': 92, 'EUR': 100, 'KZT': 0.2, 'BYN': 28, 'UAH': 2.4, 'RUB': 1 };
                                amountInRub = rawAmount * (exchangeRates[currency] || 1);
                            }

                            let roundedRub = Math.round(amountInRub);
                            
                            updateTopDonators(donation.username || 'Аноним', 'https://cdn-icons-png.flaticon.com/512/5272/5272370.png', roundedRub);

                            processTriggerEvent({
                                isGift: false,
                                giftIdStr: null,
                                donationAmount: roundedRub,
                                count: 1,
                                totalCoins: 0,
                                nickname: donation.username || 'Аноним',
                                avatar: 'https://cdn-icons-png.flaticon.com/512/5272/5272370.png',
                                giftName: 'Донат ' + (donation.amount_formatted || `${donation.amount} ${donation.currency || 'RUB'} (DA)`),
                                giftIcon: 'https://cdn-icons-png.flaticon.com/512/5272/5272370.png'
                            });
                        }
                    } catch (e) { console.error('Ошибка при парсинге данных доната:', e); }
                }
            }
        });
        daWs.on('close', () => { isDAConnecting = false; updateDaStatus('Соединение разорвано'); });
        daWs.on('error', () => { isDAConnecting = false; });
    } catch (err) {
        isDAConnecting = false; updateDaStatus(`Ошибка API: ${err.message}`);
        if (mainWindow && !mainWindow.isDestroyed()) mainWindow.webContents.send('play-error-sound');
    }
}

function handleTikTokGift(data) {
    if (timerState.isVictory || timerState.isRollingBonus) return;

    const isEnd = data.repeatEnd !== undefined ? data.repeatEnd : true;
    const giftType = data.giftType !== undefined ? data.giftType : 1; 
    if (giftType === 1 && !isEnd) return; 

    const giftIdStr = String(data.giftId || '');
    const count = data.repeatCount || 1;
    const diamonds = data.diamondCount || 0;
    const totalCoins = diamonds * count;
    
    const nickname = data.nickname || data.uniqueId || 'Зритель';
    const avatar = data.profilePictureUrl || 'https://via.placeholder.com/48';
    
    const giftName = data.extendedGiftInfo?.name || data.giftName || 'Подарок';
    const giftIcon = data.extendedGiftInfo?.icon?.url_list?.[0] || data.giftPictureUrl || '';

    if (mainWindow && !mainWindow.isDestroyed()) { 
        mainWindow.webContents.send('check-and-save-gift', { gift_id: giftIdStr, name: giftName, icon: giftIcon, cost: diamonds }); 
        if (totalCoins > 0) { 
            mainWindow.webContents.send('track-coins', { amount: totalCoins });
            updateTopDonators(nickname, avatar, totalCoins);
        }
    }

    processTriggerEvent({
        isGift: true,
        giftIdStr: giftIdStr,
        donationAmount: null,
        count: count,
        totalCoins: totalCoins,
        nickname: nickname,
        avatar: avatar,
        giftName: giftName,
        giftIcon: giftIcon
    });
}

function handleTikTokLike(data) {
    if (timerState.isVictory || timerState.isRollingBonus) return;

    const batchLikes = parseInt(data.likeCount || 1, 10);
    const apiTotalLikes = parseInt(data.totalLikeCount || 0, 10);

    if (!isNaN(apiTotalLikes) && apiTotalLikes > currentStreamTotalLikes) {
        currentStreamTotalLikes = apiTotalLikes;
    } else {
        currentStreamTotalLikes += batchLikes;
    }

    const nickname = data.nickname || 'Зритель';
    const avatar = data.profilePictureUrl || 'https://via.placeholder.com/48';
    const userId = data.uniqueId || String(Math.random());

    if (batchLikes > 0) {
        updateTopLikers(nickname, avatar, batchLikes);
    }

    let rouletteTriggered = false;
    if (timerState.settings.roulettes && currentStreamTotalLikes > 0) {
        timerState.settings.roulettes.forEach(roulette => {
            if (roulette.triggerType === 'like' || roulette.triggerType === 'both') {
                const globalThreshold = parseInt(roulette.likesThreshold, 10);
                if (globalThreshold && globalThreshold > 0) {
                    const currentMilestone = Math.floor(currentStreamTotalLikes / globalThreshold);
                    let lastMilestone = lastProcessedLikesMilestones[roulette.id];
                    
                    if (lastMilestone === undefined) {
                        lastProcessedLikesMilestones[roulette.id] = currentMilestone;
                    } else if (currentMilestone > lastMilestone) {
                        const triggerCount = currentMilestone - lastMilestone;
                        
                        for (let i = 0; i < triggerCount; i++) {
                            const milestoneTarget = (lastMilestone + 1 + i) * globalThreshold;
                            const formattedTarget = milestoneTarget >= 1000 ? `${(milestoneTarget/1000).toFixed(0)}k` : milestoneTarget;
                            
                            broadcastAlert({
                                id: Date.now() + Math.random() + i,
                                username: `Лайки (${formattedTarget})`,
                                avatar: 'https://cdn-icons-png.flaticon.com/512/833/833472.png',
                                giftName: `Рулетка: ${roulette.name || 'За лайки'}`,
                                timeAdded: 0,
                                type: 'roulette',
                                amount: 1,
                                targetTime: timerState.timeLeft,
                                originalType: 'like'
                            });

                            rouletteQueue.push({ 
                                user: {
                                    username: `Рулетка: ${roulette.name || 'За лайки'}`, 
                                    avatar: 'https://cdn-icons-png.flaticon.com/512/833/833472.png', 
                                    triggerGift: { name: `${formattedTarget} лайков`, icon: 'https://cdn-icons-png.flaticon.com/512/833/833472.png' },
                                    isLikesRoulette: true
                                },
                                slots: roulette.slots,
                                rouletteId: roulette.id
                            });
                        }
                        lastProcessedLikesMilestones[roulette.id] = currentMilestone;
                        rouletteTriggered = true;
                    }
                }
            }
        });
    }

    if (rouletteTriggered) {
        checkRouletteQueue();
    }
    
    requestBroadcastTime(); 

    if (!timerState.settings.likesEnabled) return; 
    const threshold = parseInt(timerState.settings.likeThreshold, 10); 
    const timeOffset = parseInt(timerState.settings.likeTime, 10);
    if (timeOffset === 0 || threshold <= 0) return;

    if (!timerState.userLikes[userId]) timerState.userLikes[userId] = 0;
    timerState.userLikes[userId] += batchLikes; 

    let triggerCount = Math.floor(timerState.userLikes[userId] / threshold);
    if (triggerCount > 0) {
        timerState.userLikes[userId] -= triggerCount * threshold;
        for (let i = 0; i < triggerCount; i++) { 
            if (timerState.isFrozen) {
                broadcastAlert({ id: Date.now() + Math.random() + i, username: nickname, avatar: avatar, giftName: "Лайки", timeAdded: 0, type: 'frozen_gift', originalType: 'like', amount: threshold, targetTime: timerState.timeLeft });
            } else {
                let addedTime = addTime(timeOffset, nickname, true);
                broadcastAlert({ id: Date.now() + Math.random() + i, username: nickname, avatar: avatar, timeAdded: addedTime, type: 'like', amount: threshold, targetTime: timerState.timeLeft }); 
            }
        }
        requestBroadcastTime(); // ОПТИМИЗАЦИЯ
    }
}

function handleTikTokFollow(data) {
    if (timerState.isVictory || timerState.isRollingBonus) return;
    if (!timerState.settings.subsEnabled) return;
    
    const subTimeOffset = timerState.settings.subTime; 
    if (subTimeOffset === 0) return;
    
    const userId = data.uniqueId || String(Math.random());
    const nickname = data.nickname || 'Зритель';
    const avatar = data.profilePictureUrl || 'https://via.placeholder.com/48';

    if (!timerState.subbedUsers.has(userId)) {
        timerState.subbedUsers.add(userId); 
        if (timerState.isFrozen) {
            broadcastAlert({ id: Date.now() + Math.random(), username: nickname, avatar: avatar, giftName: "Подписка", timeAdded: 0, type: 'frozen_gift', originalType: 'follow', targetTime: timerState.timeLeft });
        } else {
            let addedTime = addTime(subTimeOffset, nickname, true); 
            broadcastAlert({ id: Date.now() + Math.random(), username: nickname, avatar: avatar, timeAdded: addedTime, type: 'follow', targetTime: timerState.timeLeft }); 
        }
        requestBroadcastTime(); // ОПТИМИЗАЦИЯ
    }
}

async function connectTikTok(username) {
    if (!username) return;
    if (isConnecting) return; 

    const cleanUsername = username.replace('@', '');
    if (tiktokConnection && activeTikTokUsername === cleanUsername && isTtActive) {
        return; 
    }

    disconnectTikTok(); 
    isConnecting = true;
    
    // МОМЕНТАЛЬНАЯ ЗАГРУЗКА ИЗ ПОСТОЯННОГО КЭША
    if (mpUserCache[cleanUsername]) {
        currentStreamerInfo.username = mpUserCache[cleanUsername].nickname;
        currentStreamerInfo.avatar = mpUserCache[cleanUsername].avatar;
        updateTtStatus('Подключение к TikTok...', false);
    } else {
        updateTtStatus('Подключение к TikTok...', false);
    }

    try {
        console.log(`[DEBUG-TT] Шаг 1: Начинаем процесс подключения к: ${cleanUsername}`);
        
        let profileDataPromise = getTikTokProfile(cleanUsername);
        let profileData = null;

        if (!mpUserCache[cleanUsername]) {
            // Если нет в кэше, ждем результат
            profileData = await profileDataPromise;
        } else {
            // Если есть в кэше, просто обновляем его в фоне
            profileDataPromise.then(res => {
                if (res && res.nickname && res.avatar) {
                    mpUserCache[cleanUsername] = { nickname: res.nickname, avatar: res.avatar };
                    saveProfileCache();
                }
            });
        }
        
        let foundAvatar = profileData?.avatar || mpUserCache[cleanUsername]?.avatar || null;
        let foundNickname = profileData?.nickname || mpUserCache[cleanUsername]?.nickname || cleanUsername;

        console.log(`[DEBUG-TT] Шаг 2: Запуск WebcastPushConnection`);
        tiktokConnection = new WebcastPushConnection(cleanUsername, {
            processInitialData: false,
            enableExtendedGiftInfo: true,
            enableWebsocketUpgrade: true,
            requestPollingIntervalMs: 2000
        });

        tiktokConnection.on('connected', async (state) => {
            console.log(`[DEBUG-TT] Шаг 3: Подключено. Статус румы: ${state?.roomInfo?.status}`);
            
            if (state.roomInfo && state.roomInfo.status && state.roomInfo.status !== 2) {
                isConnecting = false;
                updateTtStatus('Офлайн (Стрим не запущен)', false);
                disconnectTikTok();
                return;
            }

            isConnecting = false;
            currentUsername = cleanUsername; 
            activeTikTokUsername = cleanUsername;

            // НАДЕЖНОЕ ПОЛУЧЕНИЕ НИКНЕЙМА ИЗ ДАННЫХ КОННЕКТОРА
            let roomData = state.roomInfo || state.availableRoom;
            if (!roomData) {
                try { roomData = tiktokConnection.roomInfo || tiktokConnection.availableRoom; } catch(e) {}
            }
            
            if (roomData && roomData.owner) {
                const owner = roomData.owner;
                
                // Если мы уже успешно спарсили нормальный никнейм (он не равен логину), 
                // мы НЕ даем API коннектора перезаписать его айдишником.
                let apiNick = owner.nickname || owner.display_id;
                if (!foundNickname || foundNickname.toLowerCase() === cleanUsername.toLowerCase()) {
                    foundNickname = apiNick || cleanUsername;
                }
                
                if (!foundAvatar || foundAvatar.includes('1055823.png') || foundAvatar.includes('2952338.png')) {
                    if (owner.avatar_large?.url_list?.length) foundAvatar = owner.avatar_large.url_list[0];
                    else if (owner.avatar_medium?.url_list?.length) foundAvatar = owner.avatar_medium.url_list[0];
                    else if (owner.avatar_thumb?.url_list?.length) foundAvatar = owner.avatar_thumb.url_list[0];
                }
                
                if (foundNickname && foundAvatar && !foundAvatar.includes('1055823.png')) {
                    mpUserCache[cleanUsername] = { nickname: foundNickname, avatar: foundAvatar };
                    saveProfileCache(); // Сохраняем надежные данные в кэш
                }
            }

            currentStreamerInfo.username = foundNickname;
            currentStreamerInfo.avatar = foundAvatar && !foundAvatar.includes('1055823.png') ? foundAvatar : 'https://cdn-icons-png.flaticon.com/512/1055/1055823.png';

            console.log('[DEBUG-TT] Итоговые данные для UI:', currentStreamerInfo);

            mpUserCache[cleanUsername] = {
                nickname: currentStreamerInfo.username,
                avatar: currentStreamerInfo.avatar
            };
            saveProfileCache();

            if (state.roomInfo && state.roomInfo.stats && state.roomInfo.stats.like_count) {
                currentStreamTotalLikes = parseInt(state.roomInfo.stats.like_count, 10) || 0;
                broadcastTime();
            }

            updateTtStatus('Успешно подключено', true);
            if (mainWindow && !mainWindow.isDestroyed()) {
                mainWindow.webContents.send('play-success-sound');
                mainWindow.webContents.send('track-stream', { username: cleanUsername });
            }
        });

        tiktokConnection.on('disconnected', () => {
            if (isConnecting) return;
            updateTtStatus('Офлайн (Стрим завершен)', false);
            disconnectTikTok();
        });

        tiktokConnection.on('error', (err) => {
            isConnecting = false;
            updateTtStatus('Ошибка подключения', false);
        });

        tiktokConnection.on('streamEnd', () => {
            updateTtStatus('Стрим завершен', false);
            disconnectTikTok();
        });

        tiktokConnection.on('gift', handleTikTokGift);
        tiktokConnection.on('like', handleTikTokLike);
        tiktokConnection.on('follow', handleTikTokFollow);
        tiktokConnection.on('social', (data) => {
             if (data.displayType && data.displayType.includes('follow')) {
                 handleTikTokFollow(data);
             }
        });

        await tiktokConnection.connect();

    } catch (err) { 
        isConnecting = false; 
        updateTtStatus(`Ошибка: ${err.message}`, false); 
        disconnectTikTok(); 
    }
}