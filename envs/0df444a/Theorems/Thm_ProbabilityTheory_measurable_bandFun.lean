-- Prove2me | Theorems.Thm_ProbabilityTheory_measurable_bandFun
-- name    : ProbabilityTheory.measurable_bandFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:33:32.366816+00:00
-- url     : https://prove2.me/theorems/3d8bab83-2472-4b3c-90c9-5d8e593fa3b2
-- title:
--   LeanLevy: ProbabilityTheory.measurable_bandFun
-- statement:
--   The band test function `1_{(s,t] × A}(u, x) · x` is measurable. Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/TimeSpacePoisson.lean#L978

import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonCompensated
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral

theorem ProbabilityTheory.measurable_bandFun : ∀ {A : Set Real},
  @MeasurableSet Real Real.measurableSpace A →
    ∀ (s t : Real),
      @Measurable (Prod Real Real) Real (@Prod.instMeasurableSpace Real Real Real.measurableSpace Real.measurableSpace)
        Real.measurableSpace
        (@Set.indicator (Prod Real Real) Real Real.instZero
          (@SProd.sprod (Set Real) (Set Real) (Set (Prod Real Real)) (@Set.instSProd Real Real)
            (@Set.Ioc Real Real.instPreorder s t) A)
          fun p => @Prod.snd Real Real p) := by sorry
