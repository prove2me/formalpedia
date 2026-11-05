-- Prove2me | Theorems.Thm_ProbabilityTheory_poissonTimeCount_add
-- name    : ProbabilityTheory.poissonTimeCount_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T23:01:01.174208+00:00
-- url     : https://prove2.me/theorems/4d3db605-307f-4ee7-8ff5-1fc6113a1283
-- title:
--   LeanLevy: ProbabilityTheory.poissonTimeCount_add
-- statement:
--   Pathwise additivity of the running count over consecutive time bands. Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/TimeSpacePoisson.lean#L135

import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonCompensated
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral

theorem ProbabilityTheory.poissonTimeCount_add : ∀ {Ω E : Type} [inst : MeasurableSpace E] {K : Nat → Ω → Nat} {X : Nat → Nat → Ω → Prod Real E} {A : Set E}
  {s t : Real},
  @MeasurableSet E inst A →
    @LE.le Real Real.instLE (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) s →
      @LE.le Real Real.instLE s t →
        ∀ (ω : Ω),
          @Eq ENNReal (@ProbabilityTheory.poissonTimeCount Ω E inst K X A t ω)
            (@HAdd.hAdd ENNReal ENNReal ENNReal (@instHAdd ENNReal ENNReal.instAdd)
              (@ProbabilityTheory.poissonTimeCount Ω E inst K X A s ω)
              (@DFunLike.coe
                (@MeasureTheory.Measure (Prod Real E) (@Prod.instMeasurableSpace Real E Real.measurableSpace inst))
                (Set (Prod Real E)) (fun x => ENNReal)
                (@MeasureTheory.Measure.instFunLike (Prod Real E)
                  (@Prod.instMeasurableSpace Real E Real.measurableSpace inst))
                (@ProbabilityTheory.poissonRandomMeasure Ω (Prod Real E)
                  (@Prod.instMeasurableSpace Real E Real.measurableSpace inst) K X ω)
                (@SProd.sprod (Set Real) (Set E) (Set (Prod Real E)) (@Set.instSProd Real E)
                  (@Set.Ioc Real Real.instPreorder s t) A))) := by sorry
