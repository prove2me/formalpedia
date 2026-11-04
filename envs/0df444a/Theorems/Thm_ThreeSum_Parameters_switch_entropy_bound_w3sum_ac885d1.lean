-- Prove2me | Theorems.Thm_ThreeSum_Parameters_switch_entropy_bound_w3sum_ac885d1
-- name    : ThreeSum.Parameters.switch_entropy_bound_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:56:32.24168+00:00
-- url     : https://prove2.me/theorems/7878765d-7491-4edf-9631-e88747974564
-- title:
--   Parameters: switch entropy bound
-- statement:
--   The entropy charge including the exact `9/mu` integer-rounding allowance.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Parameters.lean#L467-L484
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Parameters.lean#L467-L484

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

theorem ThreeSum.Parameters.switch_entropy_bound_w3sum_ac885d1 {a t mu : ℝ}
    (ha : a ∈ Icc (0 : ℝ) terminalFraction) (ht : t ∈ Icc (0 : ℝ) (1 / 2))
    (hmu : 0 < mu)
    (hswitch : phi t < switchThreshold a + 9 / ((1 - a) * mu)) :
    (1 - a) * entropy t <
      entropyRatio * (1 + boxSaving - 2 * bandShift) + 9 * entropyRatio / mu := by sorry
