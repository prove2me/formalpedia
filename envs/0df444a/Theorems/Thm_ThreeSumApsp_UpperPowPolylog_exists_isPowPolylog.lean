-- Prove2me | Theorems.Thm_ThreeSumApsp_UpperPowPolylog_exists_isPowPolylog
-- name    : ThreeSumApsp.UpperPowPolylog.exists_isPowPolylog
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:09:05.235963+00:00
-- url     : https://prove2.me/theorems/f670a20b-0e64-427e-a4fe-39bc85da3ca1
-- title:
--   Upper Pow Polylog: exists is Pow Polylog
-- statement:
--   An upper bound `Õ(n^a)` is a bound by a nonnegative function of the class `Õ(n^a)`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean#L89-L94
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean#L89-L94

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_UpperBounds
set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f f' g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.UpperPowPolylog

theorem ThreeSumApsp.UpperPowPolylog.exists_isPowPolylog (h : UpperPowPolylog f a) :
    ∃ g : ℕ → ℝ, (∀ n, 0 ≤ g n) ∧ IsPowPolylog g a ∧ ∀ᶠ n in atTop, f n ≤ g n := by sorry
