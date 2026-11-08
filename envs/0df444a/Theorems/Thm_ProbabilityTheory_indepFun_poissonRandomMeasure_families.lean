-- Prove2me | Theorems.Thm_ProbabilityTheory_indepFun_poissonRandomMeasure_families
-- name    : ProbabilityTheory.indepFun_poissonRandomMeasure_families
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:29:55.596448+00:00
-- url     : https://prove2.me/theorems/a92e7255-01c6-4058-9be5-e40a8b71159e
-- title:
--   LeanLevy: ProbabilityTheory.indepFun_poissonRandomMeasure_families
-- statement:
--   Cross-family independence: two finite families of finite-mass evaluation sets, with every set of Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonFiltration.lean#L394

import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Mathlib.MeasureTheory.PiSystem
import Definitions.Def_LeanLevy_Probability_IndependenceGrouping
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure

theorem ProbabilityTheory.indepFun_poissonRandomMeasure_families : ∀ {Ω E : Type} [inst : MeasurableSpace Ω] [inst_1 : MeasurableSpace E] {K : Nat → Ω → Nat} {X : Nat → Nat → Ω → E}
  {m : @MeasureTheory.Measure E inst_1} {μ : @MeasureTheory.Measure Ω inst}
  [inst_2 : @MeasureTheory.SigmaFinite E inst_1 m] [inst_3 : Nonempty E] [@MeasureTheory.IsProbabilityMeasure Ω inst μ],
  @ProbabilityTheory.IsPoissonPointFamily Ω E inst_1 inst K X m inst_2 inst_3 μ →
    ∀ {ιB ιC : Type} [Fintype ιB] [Fintype ιC] {B : ιB → Set E} {C : ιC → Set E},
      (∀ (i : ιB), @MeasurableSet E inst_1 (B i)) →
        (∀ (j : ιC), @MeasurableSet E inst_1 (C j)) →
          (∀ (i : ιB),
              @LT.lt ENNReal (@Preorder.toLT ENNReal (@PartialOrder.toPreorder ENNReal ENNReal.instPartialOrder))
                (@DFunLike.coe (@MeasureTheory.Measure E inst_1) (Set E) (fun x => ENNReal)
                  (@MeasureTheory.Measure.instFunLike E inst_1) m (B i))
                (@Top.top ENNReal ENNReal.instTop)) →
            (∀ (j : ιC),
                @LT.lt ENNReal (@Preorder.toLT ENNReal (@PartialOrder.toPreorder ENNReal ENNReal.instPartialOrder))
                  (@DFunLike.coe (@MeasureTheory.Measure E inst_1) (Set E) (fun x => ENNReal)
                    (@MeasureTheory.Measure.instFunLike E inst_1) m (C j))
                  (@Top.top ENNReal ENNReal.instTop)) →
              (∀ (i : ιB) (j : ιC),
                  @Disjoint (Set E)
                    (@ChainCompletePartialOrder.toPartialOrder (Set E)
                      (@ChainCompletePartialOrder.instOfCompleteLattice (Set E)
                        (@CompleteBooleanAlgebra.toCompleteLattice (Set E)
                          (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra (Set E)
                            (@Set.instCompleteAtomicBooleanAlgebra E)))))
                    (@HeytingAlgebra.toOrderBot (Set E)
                      (@Order.Frame.toHeytingAlgebra (Set E)
                        (@CompleteDistribLattice.toFrame (Set E)
                          (@CompleteBooleanAlgebra.toCompleteDistribLattice (Set E)
                            (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra (Set E)
                              (@Set.instCompleteAtomicBooleanAlgebra E))))))
                    (B i) (C j)) →
                @ProbabilityTheory.IndepFun Ω (ιB → ENNReal) (ιC → ENNReal) inst
                  (@MeasurableSpace.pi ιB (fun i => ENNReal) fun a => ENNReal.measurableSpace)
                  (@MeasurableSpace.pi ιC (fun j => ENNReal) fun a => ENNReal.measurableSpace)
                  (fun ω i =>
                    @DFunLike.coe (@MeasureTheory.Measure E inst_1) (Set E) (fun x => ENNReal)
                      (@MeasureTheory.Measure.instFunLike E inst_1)
                      (@ProbabilityTheory.poissonRandomMeasure Ω E inst_1 K X ω) (B i))
                  (fun ω j =>
                    @DFunLike.coe (@MeasureTheory.Measure E inst_1) (Set E) (fun x => ENNReal)
                      (@MeasureTheory.Measure.instFunLike E inst_1)
                      (@ProbabilityTheory.poissonRandomMeasure Ω E inst_1 K X ω) (C j))
                  μ := by sorry
