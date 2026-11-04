-- Prove2me | Theorems.Thm_ThreeSumApsp_UpperPowLittleO_upperBigOPow
-- name    : ThreeSumApsp.UpperPowLittleO.upperBigOPow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:12:44.262685+00:00
-- url     : https://prove2.me/theorems/1bc03387-96f9-42fc-9c05-6a1d97f31588
-- title:
--   Upper Pow Little O: upper Big OPow
-- statement:
--   The `o(1)` is absorbed: `n^{a+o(1)} ⊆ O(n^b)` for `a < b`, from above.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean#L161-L163
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean#L161-L163

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_UpperBounds
set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f f' g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.UpperPowLittleO

theorem ThreeSumApsp.UpperPowLittleO.upperBigOPow (h : UpperPowLittleO f a) (hab : a < b) : UpperBigOPow f b := by sorry
