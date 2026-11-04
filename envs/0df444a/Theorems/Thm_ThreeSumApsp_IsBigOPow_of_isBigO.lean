-- Prove2me | Theorems.Thm_ThreeSumApsp_IsBigOPow_of_isBigO
-- name    : ThreeSumApsp.IsBigOPow.of_isBigO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:05:46.288203+00:00
-- url     : https://prove2.me/theorems/fef52cbd-c318-4d4a-b928-9e3c68ee6451
-- title:
--   Is Big OPow: of is Big O
-- statement:
--   If `g = O(n^a)` and `f = O(g)`, then `f = O(n^a)`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L65-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L65-L66

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

theorem ThreeSumApsp.IsBigOPow.of_isBigO (hg : IsBigOPow g a) (hfg : f =O[atTop] g) : IsBigOPow f a := by sorry
