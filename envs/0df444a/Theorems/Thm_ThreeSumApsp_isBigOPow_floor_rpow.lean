-- Prove2me | Theorems.Thm_ThreeSumApsp_isBigOPow_floor_rpow
-- name    : ThreeSumApsp.isBigOPow_floor_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:12:23.62783+00:00
-- url     : https://prove2.me/theorems/8077fe17-2080-49d1-b1b2-56f2cd0be0b5
-- title:
--   Three Sum Apsp: is Big OPow floor rpow
-- statement:
--   `⌊n ^ μ⌋ = O(n^μ)`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L140-L143
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L140-L143

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

theorem ThreeSumApsp.isBigOPow_floor_rpow (μ : ℝ) : IsBigOPow (fun n : ℕ => (⌊(n : ℝ) ^ μ⌋₊ : ℝ)) μ := by sorry
