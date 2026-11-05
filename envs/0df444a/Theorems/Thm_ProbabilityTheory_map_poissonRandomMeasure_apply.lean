-- Prove2me | Theorems.Thm_ProbabilityTheory_map_poissonRandomMeasure_apply
-- name    : ProbabilityTheory.map_poissonRandomMeasure_apply
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:58:32.399771+00:00
-- url     : https://prove2.me/theorems/9dab9398-59f0-4e84-84af-88283ff138fe
-- title:
--   LeanLevy: ProbabilityTheory.map_poissonRandomMeasure_apply
-- statement:
--   **Superposition (the evaluation law).** The total number of realized points landing in a Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonRandomMeasure.lean#L438

import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily

theorem ProbabilityTheory.map_poissonRandomMeasure_apply : ∀ {Ω E : Type} [inst : MeasurableSpace E] [inst_1 : MeasurableSpace Ω] {K : Nat → Ω → Nat} {X : Nat → Nat → Ω → E}
  {m : @MeasureTheory.Measure E inst} [inst_2 : @MeasureTheory.SigmaFinite E inst m] [inst_3 : Nonempty E]
  {μ : @MeasureTheory.Measure Ω inst_1} {A : Set E} [@MeasureTheory.IsProbabilityMeasure Ω inst_1 μ],
  @ProbabilityTheory.IsPoissonPointFamily Ω E inst inst_1 K X m inst_2 inst_3 μ →
    @MeasurableSet E inst A →
      @LT.lt ENNReal (@Preorder.toLT ENNReal (@PartialOrder.toPreorder ENNReal ENNReal.instPartialOrder))
          (@DFunLike.coe (@MeasureTheory.Measure E inst) (Set E) (fun x => ENNReal)
            (@MeasureTheory.Measure.instFunLike E inst) m A)
          (@Top.top ENNReal ENNReal.instTop) →
        @Eq (@MeasureTheory.Measure ENNReal ENNReal.measurableSpace)
          (@MeasureTheory.Measure.map Ω ENNReal inst_1 ENNReal.measurableSpace
            (fun ω =>
              @DFunLike.coe (@MeasureTheory.Measure E inst) (Set E) (fun x => ENNReal)
                (@MeasureTheory.Measure.instFunLike E inst) (@ProbabilityTheory.poissonRandomMeasure Ω E inst K X ω) A)
            μ)
          (@MeasureTheory.Measure.map Nat ENNReal Nat.instMeasurableSpace ENNReal.measurableSpace
            (@Nat.cast ENNReal
              (@AddMonoidWithOne.toNatCast ENNReal
                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne)))
            (ProbabilityTheory.poissonMeasure
              (@DFunLike.coe (@MeasureTheory.Measure E inst) (Set E) (fun x => ENNReal)
                  (@MeasureTheory.Measure.instFunLike E inst) m A).toNNReal)) := by sorry
