-- Prove2me | Theorems.Thm_ProbabilityTheory_poissonSecondMoment_hasSum
-- name    : ProbabilityTheory.poissonSecondMoment_hasSum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:46:39.299721+00:00
-- url     : https://prove2.me/theorems/1cbd7a46-8552-499c-876b-e8fb85e550a9
-- title:
--   LeanLevy: ProbabilityTheory.poissonSecondMoment_hasSum
-- statement:
--   Exact theorem signature transcribed from the pinned LeanLevy source. The source section variable is made explicit; the proof remains open.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Probability/Poisson.lean#L109

import Mathlib
import Definitions.Def_LeanLevy_Probability_Poisson
open MeasureTheory Real Complex Finset ProbabilityTheory
open scoped ENNReal NNReal Nat

theorem ProbabilityTheory.poissonSecondMoment_hasSum (r : ℝ≥0) :
    HasSum (fun (n : ℕ) ↦ (↑n : ℝ) ^ 2 * (poissonMeasure r).real {n}) ((r : ℝ) ^ 2 + r) := by sorry
