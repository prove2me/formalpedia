-- Prove2me | Theorems.Thm_ThreeSumApsp_IsBigOPow_mul
-- name    : ThreeSumApsp.IsBigOPow.mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:08:01.650549+00:00
-- url     : https://prove2.me/theorems/03027eaa-c5a4-4ee8-b80e-bfa85069268b
-- title:
--   Is Big OPow: mul
-- statement:
--   `O(n^a) · O(n^b) = O(n^(a+b))`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L87-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L87-L89

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Theorems.Thm_ThreeSumApsp_Dominated_mul

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.IsBigOPow

theorem ThreeSumApsp.IsBigOPow.mul (hf : IsBigOPow f a) (hg : IsBigOPow g b) :
    IsBigOPow (fun n => f n * g n) (a + b) := by sorry
