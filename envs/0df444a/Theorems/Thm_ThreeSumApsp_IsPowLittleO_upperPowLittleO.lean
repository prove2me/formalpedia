-- Prove2me | Theorems.Thm_ThreeSumApsp_IsPowLittleO_upperPowLittleO
-- name    : ThreeSumApsp.IsPowLittleO.upperPowLittleO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:12:40.624335+00:00
-- url     : https://prove2.me/theorems/7592b63f-08c0-4b39-adf9-4eb349daa566
-- title:
--   Is Pow Little O: upper Pow Little O
-- statement:
--   `f = n^{a+o(1)}` is in particular an upper bound on `f`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean#L140-L142
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean#L140-L142

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_UpperBounds
set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f f' g : ℕ → ℝ} {a b : ℝ}

theorem ThreeSumApsp.IsPowLittleO.upperPowLittleO (hf : IsPowLittleO f a) : UpperPowLittleO f a := by sorry
