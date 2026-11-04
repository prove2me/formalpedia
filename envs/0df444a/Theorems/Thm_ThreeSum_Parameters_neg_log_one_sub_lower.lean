-- Prove2me | Theorems.Thm_ThreeSum_Parameters_neg_log_one_sub_lower
-- name    : ThreeSum.Parameters.neg_log_one_sub_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:56:08.556604+00:00
-- url     : https://prove2.me/theorems/11345237-66b5-4963-aa1c-2710e7d40fdb
-- title:
--   Parameters: neg log one sub lower
-- statement:
--   The two nonnegative initial terms of the convergent logarithm series.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Parameters.lean#L342-L349
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Parameters.lean#L342-L349

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_Parameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048

theorem ThreeSum.Parameters.neg_log_one_sub_lower {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    t + t ^ 2 / 2 ≤ -Real.log (1 - t) := by sorry
