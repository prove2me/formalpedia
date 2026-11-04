-- Prove2me | Theorems.Thm_ThreeSumApsp_isPowPolylog_rpow__8aeb32
-- name    : ThreeSumApsp.isPowPolylog_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:46:07.063326+00:00
-- url     : https://prove2.me/theorems/8aeb32a3-8e99-4d10-a39f-c4161621d760
-- title:
--   Three Sum Apsp: is Pow Polylog rpow
-- statement:
--   `n ^ a = Õ(n^a)`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L176-L177
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L176-L177

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

theorem ThreeSumApsp.isPowPolylog_rpow (a : ℝ) : IsPowPolylog (fun n : ℕ => (n : ℝ) ^ a) a := by sorry
