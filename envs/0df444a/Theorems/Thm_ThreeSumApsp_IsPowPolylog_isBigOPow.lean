-- Prove2me | Theorems.Thm_ThreeSumApsp_IsPowPolylog_isBigOPow
-- name    : ThreeSumApsp.IsPowPolylog.isBigOPow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:03:38.145771+00:00
-- url     : https://prove2.me/theorems/b6de7e99-fabe-4945-a2b1-b560a498bd73
-- title:
--   Is Pow Polylog: is Big OPow
-- statement:
--   Logarithms are absorbed: `Õ(n^a) ⊆ O(n^b)` for `a < b`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L279-L281
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L279-L281

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

theorem ThreeSumApsp.IsPowPolylog.isBigOPow (hf : IsPowPolylog f a) (hab : a < b) : IsBigOPow f b := by sorry
