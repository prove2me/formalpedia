-- Prove2me | Theorems.Thm_ProbabilityTheory_integrable_bandFun
-- name    : ProbabilityTheory.integrable_bandFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:30:55.123361+00:00
-- url     : https://prove2.me/theorems/ba1b449b-0e43-48d2-97b1-38fe79e226a2
-- title:
--   LeanLevy: ProbabilityTheory.integrable_bandFun
-- statement:
--   The band test function is integrable against `volume.prod ν` when `A ⊆ (-1, 1)` has finite mass: Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/TimeSpacePoisson.lean#L984

import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonCompensated
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral

theorem ProbabilityTheory.integrable_bandFun : ∀ {ν : @MeasureTheory.Measure Real Real.measurableSpace} [@MeasureTheory.SigmaFinite Real Real.measurableSpace ν]
  {A : Set Real},
  @MeasurableSet Real Real.measurableSpace A →
    @LE.le (Set Real) (@Set.instLE Real) A
        (@Set.Ioo Real Real.instPreorder
          (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
          (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))) →
      @LT.lt ENNReal (@Preorder.toLT ENNReal (@PartialOrder.toPreorder ENNReal ENNReal.instPartialOrder))
          (@DFunLike.coe (@MeasureTheory.Measure Real Real.measurableSpace) (Set Real) (fun x => ENNReal)
            (@MeasureTheory.Measure.instFunLike Real Real.measurableSpace) ν A)
          (@Top.top ENNReal ENNReal.instTop) →
        ∀ (s t : Real),
          @MeasureTheory.Integrable Real
            (@UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
            (@SeminormedAddGroup.toContinuousENorm Real
              (@SeminormedAddCommGroup.toSeminormedAddGroup Real
                (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Real
                  (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Real
                    (@SeminormedCommRing.toNonUnitalSeminormedCommRing Real
                      (@NormedCommRing.toSeminormedCommRing Real Real.normedCommRing))))))
            (Prod Real Real)
            (@Prod.instMeasurableSpace Real Real (@MeasureTheory.MeasureSpace.toMeasurableSpace Real Real.measureSpace)
              Real.measurableSpace)
            (@Set.indicator (Prod Real Real) Real Real.instZero
              (@SProd.sprod (Set Real) (Set Real) (Set (Prod Real Real)) (@Set.instSProd Real Real)
                (@Set.Ioc Real Real.instPreorder s t) A)
              fun p => @Prod.snd Real Real p)
            (@MeasureTheory.Measure.prod Real Real
              (@MeasureTheory.MeasureSpace.toMeasurableSpace Real Real.measureSpace) Real.measurableSpace
              (@MeasureTheory.MeasureSpace.volume Real Real.measureSpace) ν) := by sorry
