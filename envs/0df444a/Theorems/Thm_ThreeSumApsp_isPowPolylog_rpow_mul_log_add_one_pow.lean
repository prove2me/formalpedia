-- Prove2me | Theorems.Thm_ThreeSumApsp_isPowPolylog_rpow_mul_log_add_one_pow
-- name    : ThreeSumApsp.isPowPolylog_rpow_mul_log_add_one_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:12:36.670735+00:00
-- url     : https://prove2.me/theorems/14977194-45d4-4b9d-8d5c-31664ba0b5f7
-- title:
--   Three Sum Apsp: is Pow Polylog rpow mul log add one pow
-- statement:
--   `n ^ a * (log n + 1) ^ e = Õ(n^a)`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L329-L332
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L329-L332

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

theorem ThreeSumApsp.isPowPolylog_rpow_mul_log_add_one_pow (a : ℝ) (e : ℕ) :
    IsPowPolylog (fun n : ℕ => (n : ℝ) ^ a * (Real.log n + 1) ^ e) a := by sorry
