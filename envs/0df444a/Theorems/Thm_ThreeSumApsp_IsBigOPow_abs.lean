-- Prove2me | Theorems.Thm_ThreeSumApsp_IsBigOPow_abs
-- name    : ThreeSumApsp.IsBigOPow.abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:07:52.642204+00:00
-- url     : https://prove2.me/theorems/1fb960f8-3b42-4312-becd-33e346bb8ea5
-- title:
--   Is Big OPow: abs
-- statement:
--   If `f = O(n^a)` then `|f| = O(n^a)`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L106-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L106-L107

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
open ThreeSumApsp.IsBigOPow

theorem ThreeSumApsp.IsBigOPow.abs (hf : IsBigOPow f a) : IsBigOPow (fun n => |f n|) a := by sorry
