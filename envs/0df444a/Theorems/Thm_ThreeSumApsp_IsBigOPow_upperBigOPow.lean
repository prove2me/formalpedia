-- Prove2me | Theorems.Thm_ThreeSumApsp_IsBigOPow_upperBigOPow
-- name    : ThreeSumApsp.IsBigOPow.upperBigOPow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:08:01.070004+00:00
-- url     : https://prove2.me/theorems/fd009e66-bdc6-478a-8a89-7276c62aae65
-- title:
--   Is Big OPow: upper Big OPow
-- statement:
--   `f = O(n^a)` is in particular an upper bound on `f`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean#L53-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean#L53-L57

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_UpperBounds
set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f f' g : ℕ → ℝ} {a b : ℝ}

theorem ThreeSumApsp.IsBigOPow.upperBigOPow (hf : IsBigOPow f a) : UpperBigOPow f a := by sorry
