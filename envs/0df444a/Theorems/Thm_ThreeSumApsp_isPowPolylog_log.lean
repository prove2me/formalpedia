-- Prove2me | Theorems.Thm_ThreeSumApsp_isPowPolylog_log
-- name    : ThreeSumApsp.isPowPolylog_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:10:34.142725+00:00
-- url     : https://prove2.me/theorems/e566b7dd-5c48-4f09-95c9-0400b528db6f
-- title:
--   Three Sum Apsp: is Pow Polylog log
-- statement:
--   `log n = Õ(1)`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L184-L185
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L184-L185

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

theorem ThreeSumApsp.isPowPolylog_log : IsPowPolylog (fun n : ℕ => Real.log n) 0 := by sorry
