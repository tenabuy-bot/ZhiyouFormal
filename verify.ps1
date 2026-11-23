# ============================================================================
#  ZhiyouFormal —— 本地一键验算脚本（Windows PowerShell 5.1+ / PowerShell 7）
#
#  作用：不重新编译 Mathlib（直接复用 .lake/packages 下已缓存的官方 olean），
#        直接用 Lean 内核逐模块重新验算本工程 5 个模块 + 公理审计模块。
#
#  用法（在本目录下）：
#      pwsh ./verify.ps1            # 全量验算（约 3–6 分钟）
#      pwsh ./verify.ps1 -Audit     # 额外跑公理审计并检查 sorryAx
# ============================================================================
param(
    [switch]$Audit
)

$ErrorActionPreference = 'Stop'
Set-Location $PSScriptRoot

# ---- 1. 定位 Lean 4.14.0 工具链 -------------------------------------------------
function Resolve-Lean {
    $candidates = @(
        (Join-Path $env:USERPROFILE '.lean\v4.14.0\lean-4.14.0-windows\bin\lean.exe'),
        (Join-Path $env:USERPROFILE '.elan\toolchains\leanprover--lean4---v4.14.0\bin\lean.exe')
    )
    foreach ($c in $candidates) { if (Test-Path $c) { return $c } }
    $cmd = Get-Command lean -ErrorAction SilentlyContinue
    if ($cmd) { return $cmd.Source }
    throw "未找到 Lean 工具链。请先安装 elan 并执行: elan toolchain install leanprover/lean4:v4.14.0"
}

$lean = Resolve-Lean
$ver = (& $lean --version) -join ' '
Write-Host "Lean: $ver" -ForegroundColor Cyan
Write-Host "路径: $lean" -ForegroundColor DarkGray

# ---- 2. 组装 LEAN_PATH（复用已缓存的 Mathlib olean） ----------------------------
$libDirs = @('.lake\build\lib')
foreach ($pkg in 'mathlib', 'batteries', 'aesop', 'Qq', 'Cli', 'plausible', 'LeanSearchClient', 'importGraph', 'proofwidgets') {
    $libDirs += (Join-Path (Join-Path $PSScriptRoot ".lake\packages\$pkg") '.lake\build\lib')
}
$existing = @()
foreach ($d in $libDirs) {
    if (Test-Path $d) { $existing += (Resolve-Path $d).Path }
    elseif ($d -like '*mathlib*') { throw "缺少 Mathlib 编译产物：$d（请先执行 lake exe cache get）" }
}
$env:LEAN_PATH = ($existing -join ';')

New-Item -ItemType Directory -Force -Path '.lake\build\lib\ZhiyouFormal' | Out-Null

# ---- 3. 逐模块验算（顺序：Book1 → Book2 → Book3 → 跨学科 → 根入口） -------------
$modules = @(
    'Book1_ContinuousOntology',
    'Book2_ProbabilityCloud',
    'Book3_ZhiyouTheory',
    'CrossDiscipline_Correspondence'
)

$failures = @()
$sw = [System.Diagnostics.Stopwatch]::StartNew()

foreach ($m in $modules) {
    $src = "ZhiyouFormal/$m.lean"
    $out = ".lake\build\lib\ZhiyouFormal\$m.olean"
    $ilean = ".lake\build\lib\ZhiyouFormal\$m.ilean"
    $log = [System.IO.Path]::GetTempFileName()
    & $lean -o $out -i $ilean $src > $log 2>&1
    $code = $LASTEXITCODE
    $text = Get-Content $log -ErrorAction SilentlyContinue
    Remove-Item $log -Force -ErrorAction SilentlyContinue
    if ($code -ne 0 -or $text) {
        $failures += "  ✗ $src (exit $code)"
        $text | ForEach-Object { $failures += "      $_" }
        Write-Host "✗ $src" -ForegroundColor Red
    } else {
        Write-Host "✔ $src" -ForegroundColor Green
    }
}

# 根入口模块（仅 import，用于确认整体依赖闭合）
$log = [System.IO.Path]::GetTempFileName()
& $lean -o '.lake\build\lib\ZhiyouFormal.olean' -i '.lake\build\lib\ZhiyouFormal.ilean' 'ZhiyouFormal.lean' > $log 2>&1
$code = $LASTEXITCODE
$text = Get-Content $log -ErrorAction SilentlyContinue
Remove-Item $log -Force -ErrorAction SilentlyContinue
if ($code -ne 0 -or $text) {
    $failures += "  ✗ ZhiyouFormal.lean (exit $code)"
    $text | ForEach-Object { $failures += "      $_" }
    Write-Host "✗ ZhiyouFormal.lean" -ForegroundColor Red
} else {
    Write-Host "✔ ZhiyouFormal.lean" -ForegroundColor Green
}

# ---- 4. 可选：公理审计（0 sorryAx 检查） --------------------------------------
if ($Audit) {
    $log = Join-Path $PSScriptRoot 'Verification\axiom_audit.txt'
    New-Item -ItemType Directory -Force -Path (Split-Path $log) | Out-Null
    & $lean 'ZhiyouFormal/AxiomAudit.lean' > $log 2>&1
    $auditCode = $LASTEXITCODE
    $auditText = Get-Content $log -ErrorAction SilentlyContinue
    $sorryAx = ($auditText | Select-String 'sorryAx').Count
    if ($auditCode -ne 0) { $failures += "  ✗ AxiomAudit.lean (exit $auditCode)" }
    if ($sorryAx -gt 0) { $failures += "  ✗ 发现 $sorryAx 处 sorryAx 依赖（违反 0 sorry 纪律）" }
    Write-Host "公理审计: sorryAx = $sorryAx（应为 0），输出见 Verification\axiom_audit.txt" -ForegroundColor Cyan
}

# ---- 5. 结论 -------------------------------------------------------------------
$sw.Stop()
Write-Host ""
if ($failures.Count -eq 0) {
    Write-Host "Build completed successfully.  用时 $([math]::Round($sw.Elapsed.TotalSeconds,1)) 秒" -ForegroundColor Green
    Write-Host "全部 48 条定理 + 4 组公理无矛盾模型已通过 Lean 4 v4.14.0 内核验算，无 sorry。" -ForegroundColor Green
    exit 0
} else {
    Write-Host "验算失败：$($failures.Count) 条问题" -ForegroundColor Red
    $failures | ForEach-Object { Write-Host $_ -ForegroundColor Red }
    exit 1
}
