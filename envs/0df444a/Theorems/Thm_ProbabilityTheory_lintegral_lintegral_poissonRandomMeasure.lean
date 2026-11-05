-- Prove2me | Theorems.Thm_ProbabilityTheory_lintegral_lintegral_poissonRandomMeasure
-- name    : ProbabilityTheory.lintegral_lintegral_poissonRandomMeasure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:58:18.169875+00:00
-- url     : https://prove2.me/theorems/9a9416bb-933a-4691-9ec8-2a51c5fb1ca7
-- title:
--   LeanLevy: ProbabilityTheory.lintegral_lintegral_poissonRandomMeasure
-- statement:
--   **Campbell's formula** (Lebesgue form): the mean of `∫⁻ g dN` over `ω` is `∫⁻ g dm`. Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonRandomMeasure.lean#L1010

import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily

theorem ProbabilityTheory.lintegral_lintegral_poissonRandomMeasure : ∀ {Ω E : Type} [inst : MeasurableSpace E] [inst_1 : MeasurableSpace Ω] {K : Nat → Ω → Nat} {X : Nat → Nat → Ω → E}
  {m : @MeasureTheory.Measure E inst} [inst_2 : @MeasureTheory.SigmaFinite E inst m] [inst_3 : Nonempty E]
  {μ : @MeasureTheory.Measure Ω inst_1} [@MeasureTheory.IsProbabilityMeasure Ω inst_1 μ],
  @ProbabilityTheory.IsPoissonPointFamily Ω E inst inst_1 K X m inst_2 inst_3 μ →
    ∀ {g : E → ENNReal},
      @Measurable E ENNReal inst ENNReal.measurableSpace g →
        @Eq ENNReal
          (@MeasureTheory.lintegral Ω inst_1 μ fun ω =>
            @MeasureTheory.lintegral E inst (@ProbabilityTheory.poissonRandomMeasure Ω E inst K X ω) fun x => g x)
          (@MeasureTheory.lintegral E inst m fun x => g x) := by sorry
