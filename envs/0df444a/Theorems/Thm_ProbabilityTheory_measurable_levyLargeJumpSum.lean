-- Prove2me | Theorems.Thm_ProbabilityTheory_measurable_levyLargeJumpSum
-- name    : ProbabilityTheory.measurable_levyLargeJumpSum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:33:57.33585+00:00
-- url     : https://prove2.me/theorems/0fe836ce-51f1-41ed-a309-c82592c0fd5b
-- title:
--   LeanLevy: ProbabilityTheory.measurable_levyLargeJumpSum
-- statement:
--   The large-jump sum is a measurable function of the sample point. Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/TimeSpacePoisson.lean#L433

import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonCompensated
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral

theorem ProbabilityTheory.measurable_levyLargeJumpSum : ∀ {Ω : Type} [inst : MeasurableSpace Ω] {t : Real} {K : Nat → Ω → Nat} {X : Nat → Nat → Ω → Prod Real Real},
  (∀ (k : Nat), @Measurable Ω Nat inst Nat.instMeasurableSpace (K k)) →
    (∀ (k n : Nat),
        @Measurable Ω (Prod Real Real) inst
          (@Prod.instMeasurableSpace Real Real Real.measurableSpace Real.measurableSpace) (X k n)) →
      @Measurable Ω Real inst Real.measurableSpace (@ProbabilityTheory.levyLargeJumpSum Ω K X t) := by sorry
