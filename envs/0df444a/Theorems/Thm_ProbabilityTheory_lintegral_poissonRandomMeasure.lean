-- Prove2me | Theorems.Thm_ProbabilityTheory_lintegral_poissonRandomMeasure
-- name    : ProbabilityTheory.lintegral_poissonRandomMeasure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:32:52.223267+00:00
-- url     : https://prove2.me/theorems/46ed144f-4473-42f0-9224-9cc63a9b2069
-- title:
--   LeanLevy: ProbabilityTheory.lintegral_poissonRandomMeasure
-- statement:
--   **Lebesgue integral against the random measure.** The integral of a measurable `g` against the Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonRandomMeasure.lean#L968

import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily

theorem ProbabilityTheory.lintegral_poissonRandomMeasure : ∀ {Ω E : Type} [inst : MeasurableSpace E] {K : Nat → Ω → Nat} {X : Nat → Nat → Ω → E} {g : E → ENNReal},
  @Measurable E ENNReal inst ENNReal.measurableSpace g →
    ∀ (ω : Ω),
      @Eq ENNReal
        (@MeasureTheory.lintegral E inst (@ProbabilityTheory.poissonRandomMeasure Ω E inst K X ω) fun x => g x)
        (@tsum ENNReal Nat ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace
          (fun k => @Finset.sum Nat ENNReal ENNReal.instAddCommMonoid (Finset.range (K k ω)) fun n => g (X k n ω))
          (SummationFilter.unconditional Nat)) := by sorry
