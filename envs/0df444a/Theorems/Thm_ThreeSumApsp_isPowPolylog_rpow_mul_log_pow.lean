-- Prove2me | Theorems.Thm_ThreeSumApsp_isPowPolylog_rpow_mul_log_pow
-- name    : ThreeSumApsp.isPowPolylog_rpow_mul_log_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:07:43.857233+00:00
-- url     : https://prove2.me/theorems/c1c42362-02cf-4f75-a404-2e3963a9e84f
-- title:
--   Three Sum Apsp: is Pow Polylog rpow mul log pow
-- statement:
--   `n ^ a * (log n) ^ e = Õ(n^a)`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L166-L168
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L166-L168

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

theorem ThreeSumApsp.isPowPolylog_rpow_mul_log_pow (a : ℝ) (e : ℕ) :
    IsPowPolylog (fun n : ℕ => (n : ℝ) ^ a * Real.log n ^ e) a := by sorry
