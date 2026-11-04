-- Prove2me | Theorems.Thm_ThreeSumApsp_isPowPolylog_log_pow
-- name    : ThreeSumApsp.isPowPolylog_log_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:46:08.118499+00:00
-- url     : https://prove2.me/theorems/4ac61be8-3525-4320-9e15-5bac8049c9c2
-- title:
--   Three Sum Apsp: is Pow Polylog log pow
-- statement:
--   `(log n) ^ e = Õ(1)`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L180-L181
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L180-L181

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

theorem ThreeSumApsp.isPowPolylog_log_pow (e : ℕ) : IsPowPolylog (fun n : ℕ => Real.log n ^ e) 0 := by sorry
