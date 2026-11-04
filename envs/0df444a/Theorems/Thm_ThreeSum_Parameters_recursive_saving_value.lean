-- Prove2me | Theorems.Thm_ThreeSum_Parameters_recursive_saving_value
-- name    : ThreeSum.Parameters.recursive_saving_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:57:34.011958+00:00
-- url     : https://prove2.me/theorems/60650e3b-ec61-486d-b11f-9ad558ac67fa
-- title:
--   Parameters: recursive saving value
-- statement:
--   The Parameters construction uses the recursive saving value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Parameters.lean#L486-L489
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Parameters.lean#L486-L489

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

theorem ThreeSum.Parameters.recursive_saving_value :
    1 / 2 - bandShift - kappaCap - entropyRatio * (1 + boxSaving - 2 * bandShift)
      = (190893 / 1000000 : ℝ) := by sorry
