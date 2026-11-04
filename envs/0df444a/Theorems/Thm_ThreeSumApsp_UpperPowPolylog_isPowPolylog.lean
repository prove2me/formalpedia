-- Prove2me | Theorems.Thm_ThreeSumApsp_UpperPowPolylog_isPowPolylog
-- name    : ThreeSumApsp.UpperPowPolylog.isPowPolylog
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:46:19.071473+00:00
-- url     : https://prove2.me/theorems/db243a5b-610b-463d-ba80-0c8c811ba317
-- title:
--   Upper Pow Polylog: is Pow Polylog
-- statement:
--   For a function that is eventually nonnegative, the bound on `f` is a bound on `|f|`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean#L97-L100
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean#L97-L100

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_UpperBounds
import Theorems.Thm_ThreeSumApsp_IsBigOPow_isPowPolylog

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f f' g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.UpperPowPolylog

theorem ThreeSumApsp.UpperPowPolylog.isPowPolylog (h : UpperPowPolylog f a) (h0 : ∀ᶠ n in atTop, 0 ≤ f n) :
    IsPowPolylog f a := by sorry
