-- Prove2me | Theorems.Thm_ProbabilityTheory_isInfinitelyDivisible_poissonMeasure_map
-- name    : ProbabilityTheory.isInfinitelyDivisible_poissonMeasure_map
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:57:44.971716+00:00
-- url     : https://prove2.me/theorems/85ed49eb-7aa7-44da-ad0a-270bebd184b6
-- title:
--   LeanLevy: ProbabilityTheory.isInfinitelyDivisible_poissonMeasure_map
-- statement:
--   The Poisson distribution (pushed to ℝ) is infinitely divisible. For each `n`, take Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/InfiniteDivisible.lean#L114

import Definitions.Def_LeanLevy_Levy_InfiniteDivisible
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Processes_PoissonProcess
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Independence.CharacteristicFunction

theorem ProbabilityTheory.isInfinitelyDivisible_poissonMeasure_map : ∀ (r : NNReal),
  @ProbabilityTheory.IsInfinitelyDivisible Real Real.instAddCommMonoid Real.measurableSpace
    (@MeasureTheory.Measure.map Nat Real Nat.instMeasurableSpace Real.measurableSpace (@Nat.cast Real Real.instNatCast)
      (ProbabilityTheory.poissonMeasure r)) := by sorry
