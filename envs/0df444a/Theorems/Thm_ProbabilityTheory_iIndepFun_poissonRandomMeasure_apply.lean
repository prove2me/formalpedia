-- Prove2me | Theorems.Thm_ProbabilityTheory_iIndepFun_poissonRandomMeasure_apply
-- name    : ProbabilityTheory.iIndepFun_poissonRandomMeasure_apply
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:28:13.339013+00:00
-- url     : https://prove2.me/theorems/fd7694ea-192b-4e39-891f-34260e2f2425
-- title:
--   LeanLevy: ProbabilityTheory.iIndepFun_poissonRandomMeasure_apply
-- statement:
--   **Mutual independence of the counts in a finite disjoint family.** For a pairwise disjoint finite Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonRandomMeasure.lean#L948

import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily

theorem ProbabilityTheory.iIndepFun_poissonRandomMeasure_apply : ∀ {Ω E : Type} [inst : MeasurableSpace E] [inst_1 : MeasurableSpace Ω] {K : Nat → Ω → Nat} {X : Nat → Nat → Ω → E}
  {m : @MeasureTheory.Measure E inst} [inst_2 : @MeasureTheory.SigmaFinite E inst m] [inst_3 : Nonempty E]
  {μ : @MeasureTheory.Measure Ω inst_1} {ι : Type} [Fintype ι] [@MeasureTheory.IsProbabilityMeasure Ω inst_1 μ],
  @ProbabilityTheory.IsPoissonPointFamily Ω E inst inst_1 K X m inst_2 inst_3 μ →
    ∀ {A : ι → Set E},
      (∀ (i : ι), @MeasurableSet E inst (A i)) →
        (∀ (i : ι),
            @LT.lt ENNReal (@Preorder.toLT ENNReal (@PartialOrder.toPreorder ENNReal ENNReal.instPartialOrder))
              (@DFunLike.coe (@MeasureTheory.Measure E inst) (Set E) (fun x => ENNReal)
                (@MeasureTheory.Measure.instFunLike E inst) m (A i))
              (@Top.top ENNReal ENNReal.instTop)) →
          @Pairwise ι
              (@Function.onFun ι (Set E) Prop
                (@Disjoint (Set E)
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
                            (@Set.instCompleteAtomicBooleanAlgebra E)))))))
                A) →
            @ProbabilityTheory.iIndepFun Ω ι inst_1 (fun i => ENNReal) (fun x => ENNReal.measurableSpace)
              (fun i ω =>
                @DFunLike.coe (@MeasureTheory.Measure E inst) (Set E) (fun x => ENNReal)
                  (@MeasureTheory.Measure.instFunLike E inst) (@ProbabilityTheory.poissonRandomMeasure Ω E inst K X ω)
                  (A i))
              μ := by sorry
