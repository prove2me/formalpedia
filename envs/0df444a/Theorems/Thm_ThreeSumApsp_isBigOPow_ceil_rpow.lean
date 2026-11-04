-- Prove2me | Theorems.Thm_ThreeSumApsp_isBigOPow_ceil_rpow
-- name    : ThreeSumApsp.isBigOPow_ceil_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:11:41.780561+00:00
-- url     : https://prove2.me/theorems/bc21256e-766a-4041-adab-9059596aecb3
-- title:
--   Three Sum Apsp: is Big OPow ceil rpow
-- statement:
--   `⌈n ^ μ⌉ = O(n^μ)` for `μ ≥ 0`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L135-L137
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L135-L137

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}

theorem ThreeSumApsp.isBigOPow_ceil_rpow {μ : ℝ} (hμ : 0 ≤ μ) :
    IsBigOPow (fun n : ℕ => (⌈(n : ℝ) ^ μ⌉₊ : ℝ)) μ := by sorry
