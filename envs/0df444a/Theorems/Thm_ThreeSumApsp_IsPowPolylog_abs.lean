-- Prove2me | Theorems.Thm_ThreeSumApsp_IsPowPolylog_abs
-- name    : ThreeSumApsp.IsPowPolylog.abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:46:20.207277+00:00
-- url     : https://prove2.me/theorems/248f6efe-0caa-4c4c-a71a-7686af7fb506
-- title:
--   Is Pow Polylog: abs
-- statement:
--   If `f = Õ(n^a)` then `|f| = Õ(n^a)`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L269-L271
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L269-L271

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
open ThreeSumApsp.IsPowPolylog

theorem ThreeSumApsp.IsPowPolylog.abs (hf : IsPowPolylog f a) : IsPowPolylog (fun n => |f n|) a := by sorry
