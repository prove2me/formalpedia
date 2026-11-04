-- Prove2me | Theorems.Thm_ThreeSumApsp_UpperPowLittleO_exists_isPowLittleO
-- name    : ThreeSumApsp.UpperPowLittleO.exists_isPowLittleO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:46:33.26967+00:00
-- url     : https://prove2.me/theorems/bd81590b-8ce5-4f4a-8be7-b99cdfeb0c63
-- title:
--   Upper Pow Little O: exists is Pow Little O
-- statement:
--   An upper bound `n^{a+o(1)}` is a bound by a nonnegative function of the class `n^{a+o(1)}`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean#L153-L158
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean#L153-L158

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_UpperBounds
set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f f' g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.UpperPowLittleO

theorem ThreeSumApsp.UpperPowLittleO.exists_isPowLittleO (h : UpperPowLittleO f a) :
    ∃ g : ℕ → ℝ, (∀ n, 0 ≤ g n) ∧ IsPowLittleO g a ∧ ∀ᶠ n in atTop, f n ≤ g n := by sorry
