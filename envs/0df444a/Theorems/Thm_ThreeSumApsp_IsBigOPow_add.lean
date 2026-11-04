-- Prove2me | Theorems.Thm_ThreeSumApsp_IsBigOPow_add
-- name    : ThreeSumApsp.IsBigOPow.add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:01:52.65942+00:00
-- url     : https://prove2.me/theorems/6778b8c1-f2f7-43ce-974e-fe8152e48613
-- title:
--   Is Big OPow: add
-- statement:
--   `O(n^a) + O(n^a) = O(n^a)`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L82-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L82-L84

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Theorems.Thm_ThreeSumApsp_Dominated_add

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.IsBigOPow

theorem ThreeSumApsp.IsBigOPow.add (hf : IsBigOPow f a) (hg : IsBigOPow g a) :
    IsBigOPow (fun n => f n + g n) a := by sorry
