-- Prove2me | Theorems.Thm_ThreeSumApsp_UpperPowPolylog_upperBigOPow
-- name    : ThreeSumApsp.UpperPowPolylog.upperBigOPow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:46:25.481067+00:00
-- url     : https://prove2.me/theorems/985f32c7-ec9f-47e6-b34b-7f28cd95c32d
-- title:
--   Upper Pow Polylog: upper Big OPow
-- statement:
--   Logarithms are absorbed: `Õ(n^a) ⊆ O(n^b)` for `a < b`, from above.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean#L131-L133
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean#L131-L133

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_UpperBounds
set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f f' g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.UpperPowPolylog

theorem ThreeSumApsp.UpperPowPolylog.upperBigOPow (h : UpperPowPolylog f a) (hab : a < b) : UpperBigOPow f b := by sorry
