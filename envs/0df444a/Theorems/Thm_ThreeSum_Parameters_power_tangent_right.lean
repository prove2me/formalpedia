-- Prove2me | Theorems.Thm_ThreeSum_Parameters_power_tangent_right
-- name    : ThreeSum.Parameters.power_tangent_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:55:43.882507+00:00
-- url     : https://prove2.me/theorems/27085f3d-0809-47c7-8840-7bae97ef4769
-- title:
--   Parameters: power tangent right
-- statement:
--   The Parameters construction uses the power tangent right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Parameters.lean#L75-L76
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Parameters.lean#L75-L76

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

theorem ThreeSum.Parameters.power_tangent_right :
    (10000 : ℕ) ^ 500 < 2 ^ 1413 * 1411 ^ 500 := by sorry
