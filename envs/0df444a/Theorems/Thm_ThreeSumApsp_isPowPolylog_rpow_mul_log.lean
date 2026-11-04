-- Prove2me | Theorems.Thm_ThreeSumApsp_isPowPolylog_rpow_mul_log
-- name    : ThreeSumApsp.isPowPolylog_rpow_mul_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:12:27.309647+00:00
-- url     : https://prove2.me/theorems/0011490e-db68-447f-b82a-d3f8840f19e4
-- title:
--   Three Sum Apsp: is Pow Polylog rpow mul log
-- statement:
--   `n ^ a * log n = Õ(n^a)`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L171-L173
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L171-L173

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

theorem ThreeSumApsp.isPowPolylog_rpow_mul_log (a : ℝ) :
    IsPowPolylog (fun n : ℕ => (n : ℝ) ^ a * Real.log n) a := by sorry
