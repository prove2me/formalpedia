-- Prove2me | Theorems.Thm_ThreeSumApsp_isPowPolylog_log_mul_rpow
-- name    : ThreeSumApsp.isPowPolylog_log_mul_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:12:31.677408+00:00
-- url     : https://prove2.me/theorems/7ca0b175-a493-449d-8a29-f5b70aa42a7f
-- title:
--   Three Sum Apsp: is Pow Polylog log mul rpow
-- statement:
--   `log (c * n ^ κ) = Õ(1)`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L335-L342
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L335-L342

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

theorem ThreeSumApsp.isPowPolylog_log_mul_rpow (c κ : ℝ) :
    IsPowPolylog (fun n : ℕ => Real.log (c * (n : ℝ) ^ κ)) 0 := by sorry
