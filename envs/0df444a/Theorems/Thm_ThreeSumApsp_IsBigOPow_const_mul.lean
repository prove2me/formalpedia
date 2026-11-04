-- Prove2me | Theorems.Thm_ThreeSumApsp_IsBigOPow_const_mul
-- name    : ThreeSumApsp.IsBigOPow.const_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:04:31.731714+00:00
-- url     : https://prove2.me/theorems/453e5ac0-8d86-4972-a0a2-987e9511a9ce
-- title:
--   Is Big OPow: const mul
-- statement:
--   Constant factors are absorbed.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L102-L103
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L102-L103

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Theorems.Thm_ThreeSumApsp_Dominated_const_mul

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.IsBigOPow

theorem ThreeSumApsp.IsBigOPow.const_mul (hf : IsBigOPow f a) (c : ℝ) : IsBigOPow (fun n => c * f n) a := by sorry
