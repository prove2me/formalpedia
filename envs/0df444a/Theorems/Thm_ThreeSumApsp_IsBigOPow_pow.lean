-- Prove2me | Theorems.Thm_ThreeSumApsp_IsBigOPow_pow
-- name    : ThreeSumApsp.IsBigOPow.pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:10:31.444207+00:00
-- url     : https://prove2.me/theorems/4106ae76-e8d8-4232-83e7-091e68440c2e
-- title:
--   Is Big OPow: pow
-- statement:
--   `O(n^a) ^ k = O(n^(a k))` for a natural number `k`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L98-L99
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L98-L99

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Theorems.Thm_ThreeSumApsp_Dominated_pow

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.IsBigOPow

theorem ThreeSumApsp.IsBigOPow.pow (hf : IsBigOPow f a) (k : ℕ) : IsBigOPow (fun n => f n ^ k) (a * k) := by sorry
