-- Prove2me | Theorems.Thm_ThreeSumApsp_isBigOPow_inv_ceil_rpow
-- name    : ThreeSumApsp.isBigOPow_inv_ceil_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:12:25.7872+00:00
-- url     : https://prove2.me/theorems/783081a0-24bb-4d22-9abe-67a308adbc2b
-- title:
--   Three Sum Apsp: is Big OPow inv ceil rpow
-- statement:
--   `⌈n ^ μ⌉⁻¹ = O(n^(-μ))`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L146-L150
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L146-L150

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

theorem ThreeSumApsp.isBigOPow_inv_ceil_rpow (μ : ℝ) : IsBigOPow (fun n : ℕ => (⌈(n : ℝ) ^ μ⌉₊ : ℝ)⁻¹) (-μ) := by sorry
