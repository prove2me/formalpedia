-- Prove2me | Theorems.Thm_ProbabilityTheory_integral_factorialMoment_poissonMeasure
-- name    : ProbabilityTheory.integral_factorialMoment_poissonMeasure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:47:51.589238+00:00
-- url     : https://prove2.me/theorems/0e73951c-bd35-487f-92ff-2511a7ffc480
-- title:
--   LeanLevy: ProbabilityTheory.integral_factorialMoment_poissonMeasure
-- statement:
--   Exact theorem signature transcribed from the pinned LeanLevy source. The source section variable is made explicit; the proof remains open.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Probability/Poisson.lean#L167

import Mathlib
import Definitions.Def_LeanLevy_Probability_Poisson
open MeasureTheory Real Complex Finset ProbabilityTheory
open scoped ENNReal NNReal Nat

theorem ProbabilityTheory.integral_factorialMoment_poissonMeasure (r : ℝ≥0) :
    ∫ n, ((n : ℝ) * ((n : ℝ) - 1)) ∂(poissonMeasure r) = (r : ℝ) ^ 2 := by sorry
