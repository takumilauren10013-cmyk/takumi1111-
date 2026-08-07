/**
 * JapanChecker - app.js
 * -----------------------------------------------------
 * 大量のドメイン一覧(domains.txt)から、日本国内の営業対象になり得る
 * 事業者サイトを抽出し、result.csv に出力するWebアプリ。
 *
 * 起動: npm start
 * 画面: http://localhost:3000
 * -----------------------------------------------------
 */

const express = require("express");
const axios = require("axios");
const cheerio = require("cheerio");
const fs = require("fs");
const path = require("path");
const http = require("http");
const https = require("https");
const scoreConfig = require("./score_config");

// =======================================================
// 設定値 (7万件規模まで動かせるよう、環境変数で調整できるようにしてある)
// =======================================================
const PORT = process.env.PORT || 3000;
// 社外/社内の誰でもアクセスできる状態で公開するため、Basic認証をかける。
// 必ず環境変数で自分たちのID/パスワードに変更してから使うこと(デフォルトのままの公開は厳禁)。
const APP_USERNAME = process.env.APP_USERNAME || "admin";
const APP_PASSWORD = process.env.APP_PASSWORD || "changeme";
const DOMAINS_FILE = path.join(__dirname, "domains.txt");
const RESULT_FILE = path.join(__dirname, "result.csv");
const PROGRESS_FILE = path.join(__dirname, ".progress.log"); // 進捗管理用(result.csvには載らない0点ドメインもここには記録する)
const HISTORY_FILE = path.join(__dirname, "history.json"); // 過去に見つかった事業者の台帳(詳細情報つき、削除しない限り消えない)
const CALL_STATUS_FILE = path.join(__dirname, "call_status.json"); // 架電済みかどうかの記録(テレアポ用)

const MAX_TABLE_ROWS = Number(process.env.MAX_TABLE_ROWS) || 1000; // 画面の表に一度に表示する最大件数(全件はCSVで確認)

const REQUEST_TIMEOUT = Number(process.env.REQUEST_TIMEOUT) || 8000; // 1リクエストのタイムアウト(ms)
const DOMAIN_CONCURRENCY = Number(process.env.DOMAIN_CONCURRENCY) || 15; // 同時に処理するドメイン数(7万件規模ではEnvironmentで15〜30程度を推奨)
const PAGE_CONCURRENCY = Number(process.env.PAGE_CONCURRENCY) || 3; // 1ドメイン内で同時に取得する内部ページ数
const RETRY_COUNT = Number(process.env.RETRY_COUNT) || 1; // タイムアウト/接続エラー時の再試行回数
const RETRY_DELAY = Number(process.env.RETRY_DELAY) || 1000; // 再試行までの待機(ms)
const USER_AGENT =
  "Mozilla/5.0 (compatible; JapanCheckerBot/1.0; +https://example.com/bot)";

// コネクションを使い回して大量アクセス時の負荷・速度を改善する。
// maxSocketsは「同時接続数」の上限。DOMAIN_CONCURRENCY×PAGE_CONCURRENCYより
// 十分大きくしておく(例: 30×3=90に対して200なら余裕がある)。
const MAX_SOCKETS = Number(process.env.MAX_SOCKETS) || 200;
const httpAgent = new http.Agent({ keepAlive: true, maxSockets: MAX_SOCKETS });
const httpsAgent = new https.Agent({ keepAlive: true, maxSockets: MAX_SOCKETS });

function sleep(ms) {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

// 確認する内部ページ候補 (存在する場合のみ解析)
const INTERNAL_PATHS = [
  "/contact",
  "/contact/",
  "/company",
  "/company/",
  "/about",
  "/about/",
  "/access",
  "/access/",
  "/business",
  "/business/",
];

// 内部ページ候補 → CSV/スコア項目のマッピング
// (どちらかのパスが見つかれば true)
const PAGE_TYPE_MAP = {
  contact_page: ["/contact", "/contact/"],
  company_page: ["/company", "/company/"],
  access_page: ["/access", "/access/"],
  business_page: ["/business", "/business/"],
};

// 海外TLD(明確に除外したいもの)
const OVERSEAS_TLDS = [".kr", ".cn", ".tw", ".hk"];

// 都道府県一覧
const PREFECTURES = [
  "北海道","青森県","岩手県","宮城県","秋田県","山形県","福島県",
  "茨城県","栃木県","群馬県","埼玉県","千葉県","東京都","神奈川県",
  "新潟県","富山県","石川県","福井県","山梨県","長野県","岐阜県",
  "静岡県","愛知県","三重県","滋賀県","京都府","大阪府","兵庫県",
  "奈良県","和歌山県","鳥取県","島根県","岡山県","広島県","山口県",
  "徳島県","香川県","愛媛県","高知県","福岡県","佐賀県","長崎県",
  "熊本県","大分県","宮崎県","鹿児島県","沖縄県",
];

// CSVヘッダー(内部で使うキー名。この順番で出力する)
const CSV_HEADERS = [
  "domain","final_url","score","phone_exist","jp_domain","japanese_text",
  "lang_ja","business_name","japanese_address","contact_page","company_page",
  "google_map","access_page","business_page","status","reason",
];

// CSVの1行目(見出し)に出す日本語ラベル。順番はCSV_HEADERSと合わせる。
const CSV_HEADER_LABELS = {
  domain: "ドメイン",
  final_url: "アクセスできたURL",
  score: "スコア",
  phone_exist: "電話番号",
  jp_domain: "JPドメイン",
  japanese_text: "日本語検出",
  lang_ja: "lang=ja指定",
  business_name: "事業者名検出",
  japanese_address: "日本住所検出",
  contact_page: "お問い合わせページ",
  company_page: "会社概要ページ",
  google_map: "Googleマップ",
  access_page: "アクセスページ",
  business_page: "事業内容ページ",
  status: "判定",
  reason: "除外理由",
};

// 〇/×で出力する項目(true/falseの英語表記を避けるため)
const BOOLEAN_FIELDS = new Set([
  "phone_exist","jp_domain","japanese_text","lang_ja","business_name",
  "japanese_address","contact_page","company_page","google_map",
  "access_page","business_page",
]);

function boolLabel(v) {
  return v ? "〇" : "×";
}

function statusLabel(v) {
  return v === "OK" ? "対象" : "対象外";
}

// =======================================================
// 簡易 並列数制限ユーティリティ (外部ライブラリ不要)
// =======================================================
function createLimiter(concurrency) {
  let active = 0;
  const queue = [];
  const runNext = () => {
    if (active >= concurrency || queue.length === 0) return;
    active++;
    const { fn, resolve, reject } = queue.shift();
    fn()
      .then(resolve, reject)
      .finally(() => {
        active--;
        runNext();
      });
  };
  return function limit(fn) {
    return new Promise((resolve, reject) => {
      queue.push({ fn, resolve, reject });
      runNext();
    });
  };
}

// =======================================================
// 検出ロジック
// =======================================================

// 日本の電話番号 (必須条件)
const PHONE_REGEX =
  /(?<!\d)0\d{1,4}-\d{1,4}-\d{4}(?!\d)|(?<!\d)0\d{9,10}(?!\d)/;

function hasJapanesePhone(text) {
  return PHONE_REGEX.test(text);
}

// JPドメイン判定
function isJpDomain(domain) {
  return /\.jp$/i.test(domain.trim());
}

// 海外TLD判定
function isOverseasTld(domain) {
  const d = domain.toLowerCase();
  return OVERSEAS_TLDS.some((tld) => d.endsWith(tld));
}

// ひらがな・カタカナ検出
function hasJapaneseText(text) {
  return /[ぁ-んァ-ヶー]/.test(text);
}

// ハングル大量検出 (しきい値: 30文字以上)
function hasHeavyHangul(text) {
  const matches = text.match(/[\uAC00-\uD7A3]/g);
  return !!matches && matches.length >= 30;
}

// 中国語(簡体字/繁体字圏)の可能性が高いかどうかの簡易判定
// 「漢字は大量にあるが、ひらがな/カタカナが全く無い」場合に疑わしいと判定
function isLikelyChineseOnly(text) {
  const hanMatches = text.match(/[\u4E00-\u9FFF]/g);
  const hasKana = hasJapaneseText(text);
  return !!hanMatches && hanMatches.length >= 80 && !hasKana;
}

// 事業者名検出
const BUSINESS_NAME_REGEX =
  /(株式会社|有限会社|合同会社|合資会社|合名会社|一般社団法人|一般財団法人|[一-龠ぁ-んァ-ヶー]{2,10}(商店|工務店|建設|不動産|工業|製作所|サービス|商会))/;

function hasBusinessName(text) {
  return BUSINESS_NAME_REGEX.test(text);
}

// 日本住所検出
const POSTAL_REGEX = /〒?\s?\d{3}-\d{4}/;

function hasJapaneseAddress(text) {
  if (POSTAL_REGEX.test(text)) return true;
  return PREFECTURES.some((pref) => text.includes(pref));
}

// html lang="ja" 判定
function hasLangJa($) {
  const lang = ($("html").attr("lang") || "").toLowerCase();
  return lang.startsWith("ja");
}

// Googleマップ検出
function hasGoogleMap(html) {
  return /maps\.google\.com|google\.[a-z.]+\/maps|<iframe[^>]+src=["'][^"']*maps/i.test(
    html
  );
}

// =======================================================
// HTTP取得
// =======================================================

async function fetchUrlOnce(url) {
  const res = await axios.get(url, {
    timeout: REQUEST_TIMEOUT,
    maxRedirects: 5,
    headers: { "User-Agent": USER_AGENT },
    validateStatus: (s) => s >= 200 && s < 400,
    responseType: "text",
    transformResponse: [(data) => data], // 生のHTML文字列のまま受け取る
    httpAgent,
    httpsAgent,
  });
  return res;
}

// 一時的な接続エラー(タイムアウト・リセット等)は RETRY_COUNT 回まで再試行する。
// 404等の応答があった場合や、再試行しても無意味なエラーは即座に諦める。
async function fetchUrl(url) {
  let lastErr;
  for (let attempt = 0; attempt <= RETRY_COUNT; attempt++) {
    try {
      return await fetchUrlOnce(url);
    } catch (err) {
      lastErr = err;
      const retryable =
        !err.response && // レスポンス自体が返っていない(接続レベルの失敗)
        ["ECONNABORTED", "ECONNRESET", "ETIMEDOUT", "EAI_AGAIN"].includes(err.code) ||
        /timeout/i.test(err.message || "");
      if (!retryable || attempt === RETRY_COUNT) break;
      await sleep(RETRY_DELAY);
    }
  }
  throw lastErr;
}

// https:// を優先し、失敗したら http:// にフォールバック
async function fetchTopPage(domain) {
  const candidates = [`https://${domain}`, `http://${domain}`];
  let lastError = null;

  for (const url of candidates) {
    try {
      const res = await fetchUrl(url);
      return {
        ok: true,
        finalUrl: (res.request && res.request.res && res.request.res.responseUrl) || url,
        html: res.data || "",
      };
    } catch (err) {
      lastError = err;
    }
  }

  const timedOut =
    lastError &&
    (lastError.code === "ECONNABORTED" || /timeout/i.test(lastError.message || ""));

  return {
    ok: false,
    reason: timedOut ? "タイムアウト" : "アクセス不可",
  };
}

// 内部ページ候補を並列取得(存在するものだけ結果に含める)
async function fetchInternalPages(baseUrl) {
  const limit = createLimiter(PAGE_CONCURRENCY);
  const found = {}; // path -> html

  await Promise.all(
    INTERNAL_PATHS.map((p) =>
      limit(async () => {
        try {
          const url = new URL(p, baseUrl).toString();
          const res = await fetchUrl(url);
          found[p] = res.data || "";
        } catch (e) {
          // 存在しない/取得失敗は無視してよい(必須ではない)
        }
      })
    )
  );

  return found;
}

// =======================================================
// 1ドメインの処理
// =======================================================

async function checkDomain(rawDomain) {
  const domain = rawDomain.trim();
  const base = {
    domain,
    final_url: "",
    score: 0,
    phone_exist: false,
    jp_domain: false,
    japanese_text: false,
    lang_ja: false,
    business_name: false,
    japanese_address: false,
    contact_page: false,
    company_page: false,
    google_map: false,
    access_page: false,
    business_page: false,
    status: "NG",
    reason: "",
  };

  if (!domain) return null;

  // 海外TLDは即除外
  if (isOverseasTld(domain)) {
    return { ...base, reason: "海外TLD" };
  }

  // トップページ取得
  const top = await fetchTopPage(domain);
  if (!top.ok) {
    return { ...base, reason: top.reason };
  }

  base.final_url = top.finalUrl;

  // 内部ページ取得
  const internalPages = await fetchInternalPages(top.finalUrl);

  // 全文結合(判定用)
  const allHtml = [top.html, ...Object.values(internalPages)].join("\n");
  const $ = cheerio.load(top.html || "");
  const allText = cheerio.load(allHtml)("body").text() || allHtml;

  // 除外条件チェック
  if (hasHeavyHangul(allText)) {
    return { ...base, final_url: top.finalUrl, reason: "ハングル大量検出" };
  }
  if (isLikelyChineseOnly(allText)) {
    return { ...base, final_url: top.finalUrl, reason: "中国語大量検出の可能性" };
  }

  // 必須条件: 日本電話番号
  base.phone_exist = hasJapanesePhone(allText);
  if (!base.phone_exist) {
    return { ...base, reason: "電話番号未検出" };
  }

  // 内部ページ種別判定 (どちらかの候補パスが取得できていればtrue)
  for (const [field, paths] of Object.entries(PAGE_TYPE_MAP)) {
    base[field] = paths.some((p) => internalPages[p] !== undefined);
  }

  // スコアリング用フラグ
  base.jp_domain = isJpDomain(domain);
  base.japanese_text = hasJapaneseText(allText);
  base.lang_ja = hasLangJa($);
  base.business_name = hasBusinessName(allText);
  base.japanese_address = hasJapaneseAddress(allText);
  base.google_map = hasGoogleMap(allHtml);

  // スコア合算 (score_config.js の値だけを見る)
  let score = 0;
  for (const key of Object.keys(scoreConfig)) {
    if (base[key]) score += scoreConfig[key];
  }
  base.score = score;
  base.status = "OK";
  base.reason = "";

  return base;
}

// =======================================================
// CSV出力
// =======================================================

function csvEscape(value) {
  const str = value === undefined || value === null ? "" : String(value);
  if (/[",\n]/.test(str)) {
    return `"${str.replace(/"/g, '""')}"`;
  }
  return str;
}

function rowToCsvLine(row) {
  return (
    CSV_HEADERS.map((h) => {
      let value = row[h];
      if (BOOLEAN_FIELDS.has(h)) value = boolLabel(value);
      else if (h === "status") value = statusLabel(value);
      return csvEscape(value);
    }).join(",") + "\n"
  );
}

// 内部表現(row)を、画面表示用に日本語ラベルのキーへ変換する
function rowToDisplayRow(row) {
  const obj = {};
  CSV_HEADERS.forEach((h) => {
    let value = row[h];
    if (BOOLEAN_FIELDS.has(h)) value = boolLabel(value);
    else if (h === "status") value = statusLabel(value);
    obj[CSV_HEADER_LABELS[h]] = value;
  });
  return obj;
}

// 引用符付きCSVの1行を配列に分解する簡易パーサー(new_domains.csvの表示用)
function parseCsvLine(line) {
  const result = [];
  let cur = "";
  let inQuotes = false;
  for (let i = 0; i < line.length; i++) {
    const c = line[i];
    if (inQuotes) {
      if (c === '"') {
        if (line[i + 1] === '"') {
          cur += '"';
          i++;
        } else {
          inQuotes = false;
        }
      } else {
        cur += c;
      }
    } else if (c === '"') {
      inQuotes = true;
    } else if (c === ",") {
      result.push(cur);
      cur = "";
    } else {
      cur += c;
    }
  }
  result.push(cur);
  return result;
}

// =======================================================
// 新規事業者の検出用「台帳」(history.json)
// -------------------------------------------------------
// 1行に1件のJSONを書く形式(NDJSON)で保存する。
// 見つかるたびに1行ずつ追記するだけなので、7万件規模でも
// 「実行が全部終わるまでファイルに保存されない」ということが起きず、
// 実行中でも未架電リストにリアルタイムで反映される。
// 同じドメインを再チェックした場合は、新しい行が追加される
// (読み込み時に「そのドメインの一番新しい行」だけを使う)。
// =======================================================

// ファイルを読み込み、ドメインごとに最新の行だけを残したMapを返す。
// 旧バージョン(1つの大きなJSONオブジェクトとして保存していた形式)も読み込めるようにしてある。
function loadHistoryMap() {
  const map = new Map();
  if (!fs.existsSync(HISTORY_FILE)) return map;

  const content = fs.readFileSync(HISTORY_FILE, "utf-8").trim();
  if (!content) return map;

  const lines = content.split(/\r?\n/).filter((l) => l.length > 0);
  let allLinesAreValidEntries = true;
  const parsedLines = [];

  for (const line of lines) {
    try {
      const obj = JSON.parse(line);
      if (!obj || !obj.domain || !obj.row) {
        allLinesAreValidEntries = false;
        break;
      }
      parsedLines.push(obj);
    } catch (e) {
      allLinesAreValidEntries = false;
      break;
    }
  }

  if (allLinesAreValidEntries && parsedLines.length > 0) {
    // 新形式(NDJSON)。同じドメインが複数回出てきたら、後の行(=新しい方)で上書きする
    parsedLines.forEach((entry) => map.set(entry.domain, entry));
    return map;
  }

  // 旧形式(1つの大きなJSONオブジェクト)を試す(過去バージョンとの互換用)
  try {
    const obj = JSON.parse(content);
    Object.entries(obj).forEach(([domain, entry]) => {
      if (entry && entry.row) {
        map.set(domain, {
          domain,
          firstSeenAt: entry.firstSeenAt,
          lastCheckedAt: entry.lastCheckedAt || entry.firstSeenAt,
          row: entry.row,
        });
      }
      // さらに古い形式({firstSeenAt, score}のみ)は詳細情報が無いため復元できず、対象外とする
    });
  } catch (e) {
    // どちらの形式でもなければ空として扱う
  }
  return map;
}

// 1件分の履歴を末尾に追記する(ファイル全体の書き直しはしない = 件数が増えても速度が落ちない)
function appendHistoryEntry(entry) {
  fs.appendFileSync(HISTORY_FILE, JSON.stringify(entry) + "\n", "utf-8");
}

// 履歴ファイルを整理する(同じドメインの重複行をまとめて、最新の状態だけを残す)。
// 何度も再チェックを繰り返してファイルが大きくなってきたときに使う。
function compactHistoryFile() {
  const map = loadHistoryMap();
  const lines = [...map.values()].map((entry) => JSON.stringify(entry)).join("\n");
  fs.writeFileSync(HISTORY_FILE, lines ? lines + "\n" : "", "utf-8");
  return map.size;
}

// =======================================================
// 架電済みステータス(テレアポ用)
// =======================================================

// { "example.co.jp": { called: true, calledAt: "2026-08-06T..." }, ... }
function loadCallStatus() {
  if (!fs.existsSync(CALL_STATUS_FILE)) return {};
  try {
    return JSON.parse(fs.readFileSync(CALL_STATUS_FILE, "utf-8"));
  } catch (e) {
    return {};
  }
}

function saveCallStatus(status) {
  fs.writeFileSync(CALL_STATUS_FILE, JSON.stringify(status, null, 2), "utf-8");
}

// 台帳(history)から「まだ架電していない」事業者を、発見が新しい順に並べて返す。
// 見つかった時期に関わらず、架電済みでないものはずっとここに残り続ける。
// (実行中でも、その時点までにファイルへ書き込まれた分がそのまま反映される)
function buildUncalledLeads(limit) {
  const historyMap = loadHistoryMap();
  const callStatus = loadCallStatus();

  const entries = [...historyMap.entries()]
    .filter(([domain]) => !(callStatus[domain] && callStatus[domain].called))
    .sort((a, b) => new Date(b[1].firstSeenAt) - new Date(a[1].firstSeenAt));

  const totalRows = entries.length;
  const limited = limit ? entries.slice(0, limit) : entries;
  const rows = limited.map(([, entry]) => {
    const displayRow = rowToDisplayRow(entry.row);
    displayRow.__called = false;
    return displayRow;
  });

  return { rows, entries: limited, totalRows, truncated: totalRows > rows.length };
}
function loadCsvRows(file, limit) {
  if (!fs.existsSync(file)) {
    return { headers: [], rows: [], totalRows: 0, truncated: false };
  }
  const content = fs.readFileSync(file, "utf-8");
  const lines = content.split(/\r?\n/).filter((l) => l.length > 0);
  if (lines.length === 0) {
    return { headers: [], rows: [], totalRows: 0, truncated: false };
  }
  const headers = parseCsvLine(lines[0]);
  const dataLines = lines.slice(1);
  const totalRows = dataLines.length;
  const limited = limit ? dataLines.slice(0, limit) : dataLines;
  const rows = limited.map((line) => {
    const cells = parseCsvLine(line);
    const obj = {};
    headers.forEach((h, i) => (obj[h] = cells[i] ?? ""));
    return obj;
  });
  return { headers, rows, totalRows, truncated: totalRows > rows.length };
}

// =======================================================
// 実行状態管理 (途中経過の確認・多重実行防止用)
// =======================================================

const state = {
  running: false,
  stopRequested: false,
  resumed: false,
  total: 0,
  alreadyDone: 0, // レジューム時、前回までに処理済みだった件数
  processed: 0, // 今回のセッションで処理した件数
  matched: 0,
  skipped: 0, // 停止要求後にスキップした件数
  zeroScoreSkipped: 0, // スコア0でCSVに書かなかった件数
  newFound: 0, // 今回の実行で新しく見つかった件数
  startedAt: null,
  finishedAt: null,
  lastError: null,
};

// "https://example.com/company" や "www.example.jp/" のように
// プロトコル・パス・末尾スラッシュが付いていても、ドメイン名だけを取り出す。
function normalizeDomain(raw) {
  let s = (raw || "").trim();
  if (!s) return "";

  // 先頭にプロトコルが無ければ、URLとして解析するために一時的に付与する
  const withScheme = /^https?:\/\//i.test(s) ? s : `https://${s}`;

  try {
    const hostname = new URL(withScheme).hostname;
    return hostname.toLowerCase();
  } catch (e) {
    // URLとして解析できない特殊な入力は、簡易的にプロトコルとパスを手で除去する
    return s
      .replace(/^https?:\/\//i, "")
      .replace(/\/.*$/, "")
      .toLowerCase();
  }
}

function readDomains() {
  if (!fs.existsSync(DOMAINS_FILE)) return [];
  const content = fs.readFileSync(DOMAINS_FILE, "utf-8");
  const lines = content
    .split(/\r?\n/)
    .map((l) => normalizeDomain(l))
    .filter((l) => l.length > 0);

  // 同じドメインが重複していたら1件にまとめる(順序は維持)
  return [...new Set(lines)];
}

// 前回までに「チェック済み」だったドメインを読み取る(レジューム用)。
// result.csv はスコア0のドメインを載せないため、進捗管理は別ファイル(.progress.log)で行う。
function loadAlreadyProcessedDomains() {
  const done = new Set();
  if (!fs.existsSync(PROGRESS_FILE)) return done;

  const content = fs.readFileSync(PROGRESS_FILE, "utf-8");
  content
    .split(/\r?\n/)
    .map((l) => l.trim())
    .filter((l) => l.length > 0)
    .forEach((d) => done.add(d));
  return done;
}

// domains.txt を読み込み、1件ずつ処理して result.csv に逐次書き込む。
// 途中でプロセスが止まっても、それまでの結果はファイルに残る。
// resume=true の場合、前回の result.csv に既に記録されているドメインはスキップし、
// 続きから再開する(result.csvは上書きせず追記する)。
async function runCheck(resume) {
  if (state.running) return;

  const allDomains = readDomains();
  const alreadyDone = resume ? loadAlreadyProcessedDomains() : new Set();
  const remaining = allDomains.filter((d) => !alreadyDone.has(d));
  const historyMap = loadHistoryMap(); // 過去に見つかった事業者の台帳(ドメイン→詳細情報)

  state.running = true;
  state.stopRequested = false;
  state.resumed = !!resume;
  state.total = allDomains.length;
  state.alreadyDone = alreadyDone.size;
  state.processed = 0;
  state.matched = 0;
  state.skipped = 0;
  state.newFound = 0;
  state.startedAt = new Date();
  state.finishedAt = null;
  state.lastError = null;

  // resumeでない、またはファイルが無い場合のみヘッダーを書いて新規作成。
  // resumeの場合は追記モードで開く(既存の行はそのまま残す)。
  const isFreshFile = !resume || !fs.existsSync(RESULT_FILE);
  const writeStream = fs.createWriteStream(RESULT_FILE, {
    flags: isFreshFile ? "w" : "a",
  });
  if (isFreshFile) {
    writeStream.write(CSV_HEADERS.map((h) => CSV_HEADER_LABELS[h]).join(",") + "\n");
  }

  // 進捗ログも同じタイミングで新規/追記を切り替える
  const progressStream = fs.createWriteStream(PROGRESS_FILE, {
    flags: isFreshFile ? "w" : "a",
  });

  const limit = createLimiter(DOMAIN_CONCURRENCY);

  try {
    await Promise.all(
      remaining.map((domain) =>
        limit(async () => {
          // 停止要求が来ていたら、これ以上ネットワークアクセスせずスキップする
          if (state.stopRequested) {
            state.skipped++;
            return;
          }

          let result;
          try {
            result = await checkDomain(domain);
          } catch (err) {
            result = {
              domain,
              final_url: "",
              score: 0,
              phone_exist: false,
              jp_domain: false,
              japanese_text: false,
              lang_ja: false,
              business_name: false,
              japanese_address: false,
              contact_page: false,
              company_page: false,
              google_map: false,
              access_page: false,
              business_page: false,
              status: "NG",
              reason: "予期せぬエラー",
            };
          }
          if (result) {
            state.processed++;
            if (result.status === "OK") state.matched++;

            // スコア0のものはCSVに書き込まない(除外理由の記録は行わない)
            if (result.score > 0) {
              writeStream.write(rowToCsvLine(result));

              // 台帳(history)に詳細情報を保存する。見つかった瞬間にファイルへ追記するので、
              // 実行が終わるのを待たずに「未架電リスト」へリアルタイムで反映される。
              // 初めて見つかったドメインは firstSeenAt を記録し、以後は上書きしない。
              const existing = historyMap.get(domain);
              if (!existing) {
                const entry = {
                  domain,
                  firstSeenAt: new Date().toISOString(),
                  lastCheckedAt: new Date().toISOString(),
                  row: result,
                };
                historyMap.set(domain, entry);
                appendHistoryEntry(entry);
                state.newFound++;
              } else {
                existing.row = result;
                existing.lastCheckedAt = new Date().toISOString();
                appendHistoryEntry(existing); // firstSeenAtは既存のものを引き継ぐ
              }
            } else {
              state.zeroScoreSkipped++;
            }

            // チェック済みであることは(スコアに関わらず)進捗ログに残す
            progressStream.write(domain + "\n");
          }
        })
      )
    );
  } catch (err) {
    state.lastError = err.message;
  } finally {
    writeStream.end();
    progressStream.end();
    state.running = false;
    state.finishedAt = new Date();
  }
}

// =======================================================
// Express サーバー
// =======================================================

const app = express();

// ---- Basic認証(ここを通らないと画面もAPIも一切見えない) ----
function basicAuth(req, res, next) {
  const header = req.headers.authorization || "";
  const [scheme, encoded] = header.split(" ");

  if (scheme === "Basic" && encoded) {
    const decoded = Buffer.from(encoded, "base64").toString("utf-8");
    const separatorIndex = decoded.indexOf(":");
    const user = decoded.slice(0, separatorIndex);
    const pass = decoded.slice(separatorIndex + 1);
    if (user === APP_USERNAME && pass === APP_PASSWORD) {
      return next();
    }
  }

  res.set("WWW-Authenticate", 'Basic realm="JapanChecker", charset="UTF-8"');
  res.status(401).send("認証が必要です(IDとパスワードを入力してください)");
}

app.use(basicAuth);
// ---- ここまでBasic認証 ----

app.use(express.static(path.join(__dirname, "public")));
app.use(express.json({ limit: "5mb" })); // ドメインを大量に貼り付けても壊れないように上限を広げる

app.get("/", (req, res) => {
  res.sendFile(path.join(__dirname, "public", "index.html"));
});

// 現在のdomains.txtの中身を取得する
app.get("/api/domains", (req, res) => {
  const text = fs.existsSync(DOMAINS_FILE) ? fs.readFileSync(DOMAINS_FILE, "utf-8") : "";
  const count = readDomains().length; // 正規化・重複除去した後の実際の件数
  res.json({ text, count });
});

// domains.txt を画面から丸ごと保存(上書き)する
app.post("/api/domains", (req, res) => {
  if (state.running) {
    return res.status(409).json({ error: "実行中はドメイン一覧を変更できません。停止してから保存してください。" });
  }
  const text = (req.body && req.body.text) || "";
  fs.writeFileSync(DOMAINS_FILE, text, "utf-8");
  const count = readDomains().length;
  res.json({ ok: true, count });
});

// 実行開始 (非同期で走らせ、即座にレスポンスを返す)
// body: { resume: true } を渡すと、前回のresult.csvの続きから再開する
app.post("/api/start", (req, res) => {
  if (state.running) {
    return res.status(409).json({ error: "既に実行中です" });
  }
  const domains = readDomains();
  if (domains.length === 0) {
    return res.status(400).json({ error: "domains.txt にドメインがありません" });
  }
  const resume = !!(req.body && req.body.resume);
  runCheck(resume); // await しない(バックグラウンド実行)
  res.json({ started: true, total: domains.length, resume });
});

// 停止要求(実行中のリクエストはキャンセルできないが、
// 未着手の分はこれ以降アクセスせず打ち切る。result.csvはそれまでの分が残る)
app.post("/api/stop", (req, res) => {
  if (!state.running) {
    return res.status(409).json({ error: "実行中ではありません" });
  }
  state.stopRequested = true;
  res.json({ stopping: true });
});

// 履歴ファイル(history.json)を整理する。
// 同じドメインが何度も再チェックされていると行が重複して増えていくので、
// ドメインごとに最新の1行だけを残してファイルを小さくする。
app.post("/api/compact-history", (req, res) => {
  if (state.running) {
    return res.status(409).json({ error: "実行中は整理できません。停止してから実行してください。" });
  }
  const count = compactHistoryFile();
  res.json({ ok: true, count });
});

// 進捗確認
app.get("/api/status", (req, res) => {
  const elapsedMs = state.startedAt
    ? (state.finishedAt || new Date()) - new Date(state.startedAt)
    : 0;
  const remaining = state.total - state.alreadyDone - state.processed - state.skipped;
  const avgMsPerDomain = state.processed > 0 ? elapsedMs / state.processed : null;
  const etaMs =
    state.running && avgMsPerDomain !== null && remaining > 0
      ? Math.round(avgMsPerDomain * remaining)
      : null;

  res.json({ ...state, elapsedMs, remaining: Math.max(remaining, 0), etaMs });
});

// 結果CSVダウンロード(全結果)
app.get("/api/download", (req, res) => {
  if (!fs.existsSync(RESULT_FILE)) {
    return res.status(404).json({ error: "result.csv がまだありません" });
  }
  res.download(RESULT_FILE, "result.csv");
});

// 新規発見リストCSVダウンロード(見つかった時期に関わらず、まだ架電していない事業者を全て出力)
app.get("/api/download-new", (req, res) => {
  const { entries } = buildUncalledLeads(null); // limitなし = 全件
  let csv = CSV_HEADERS.map((h) => CSV_HEADER_LABELS[h]).join(",") + "\n";
  entries.forEach(([, entry]) => {
    csv += rowToCsvLine(entry.row);
  });
  res.setHeader("Content-Type", "text/csv; charset=utf-8");
  res.setHeader(
    "Content-Disposition",
    'attachment; filename="uncalled_list.csv"; filename*=UTF-8\'\'%E6%9C%AA%E6%9E%B6%E9%9B%BB%E3%83%AA%E3%82%B9%E3%83%88.csv'
  );
  res.send(csv);
});

// 未架電リスト(見つかった時期に関わらず、まだ架電していない事業者は全て含む)を画面表示用に返す
app.get("/api/new-list", (req, res) => {
  const headers = CSV_HEADERS.map((h) => CSV_HEADER_LABELS[h]);
  const { rows, totalRows, truncated } = buildUncalledLeads(MAX_TABLE_ROWS);
  res.json({ headers, rows, totalRows, truncated });
});

// 全結果リストを画面表示用にJSONで返す(架電済みステータスも合わせて返す)
app.get("/api/result-list", (req, res) => {
  const { headers, rows, totalRows, truncated } = loadCsvRows(RESULT_FILE, MAX_TABLE_ROWS);
  const callStatus = loadCallStatus();
  const domainKey = headers[0];
  rows.forEach((row) => {
    const cs = callStatus[row[domainKey]];
    row.__called = !!(cs && cs.called);
  });
  res.json({ headers, rows, totalRows, truncated });
});

// 架電済みステータスの取得
app.get("/api/call-status", (req, res) => {
  res.json(loadCallStatus());
});

// 架電済みステータスの更新(1件ずつ)
app.post("/api/call-status", (req, res) => {
  const { domain, called } = req.body || {};
  if (!domain) {
    return res.status(400).json({ error: "domainが必要です" });
  }
  const status = loadCallStatus();
  status[domain] = {
    called: !!called,
    calledAt: called ? new Date().toISOString() : null,
  };
  saveCallStatus(status);
  res.json({ ok: true, domain, called: !!called });
});

app.listen(PORT, () => {
  console.log(`JapanChecker running: http://localhost:${PORT}`);
  if (APP_PASSWORD === "changeme") {
    console.warn(
      "\n[警告] パスワードが初期値(changeme)のままです。社内で共有する前に、必ず環境変数 APP_USERNAME / APP_PASSWORD を設定してください。\n" +
        '例: $env:APP_USERNAME="yourname"; $env:APP_PASSWORD="好きなパスワード"; npm start\n'
    );
  }
});
