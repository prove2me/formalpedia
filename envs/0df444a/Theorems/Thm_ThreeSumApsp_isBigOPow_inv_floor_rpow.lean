-- Prove2me | Theorems.Thm_ThreeSumApsp_isBigOPow_inv_floor_rpow
-- name    : ThreeSumApsp.isBigOPow_inv_floor_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:12:26.538041+00:00
-- url     : https://prove2.me/theorems/f8c22a3c-c230-4182-bfa0-40c6138fe79c
-- title:
--   Three Sum Apsp: is Big OPow inv floor rpow
-- statement:
--   `⌊n ^ μ⌋⁻¹ = O(n^(-μ))` for `μ ≥ 0`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L153-L161
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L153-L161

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

theorem ThreeSumApsp.isBigOPow_inv_floor_rpow {μ : ℝ} (hμ : 0 ≤ μ) :
    IsBigOPow (fun n : ℕ => (⌊(n : ℝ) ^ μ⌋₊ : ℝ)⁻¹) (-μ) := by sorry
