-- Prove2me | Theorems.Thm_ProbabilityTheory_iIndepSets_piiUnionInter_of_pairwiseDisjoint
-- name    : ProbabilityTheory.iIndepSets.piiUnionInter_of_pairwiseDisjoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:55:45.992113+00:00
-- url     : https://prove2.me/theorems/c5cf4eb0-0476-4651-9970-63e91aa311f9
-- title:
--   LeanLevy: ProbabilityTheory.iIndepSets.piiUnionInter_of_pairwiseDisjoint
-- statement:
--   Mutual independence of π-systems is preserved by grouping along pairwise-disjoint Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Probability/IndependenceGrouping.lean#L40

import Definitions.Def_LeanLevy_Probability_IndependenceGrouping
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.PiSystem

universe u_1 u_2 u_3
theorem ProbabilityTheory.iIndepSets.piiUnionInter_of_pairwiseDisjoint : ∀ {Ω : Type u_1} {ι : Type u_2} {κ : Type u_3} {mΩ : MeasurableSpace Ω} {μ : @MeasureTheory.Measure Ω mΩ}
  {π : κ → Set (Set Ω)} {S : ι → Set κ},
  @ProbabilityTheory.iIndepSets Ω κ mΩ π μ →
    @Pairwise ι
        (@Function.onFun ι (Set κ) Prop
          (@Disjoint (Set κ)
            (@ChainCompletePartialOrder.toPartialOrder (Set κ)
              (@ChainCompletePartialOrder.instOfCompleteLattice (Set κ)
                (@CompleteBooleanAlgebra.toCompleteLattice (Set κ)
                  (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra (Set κ)
                    (@Set.instCompleteAtomicBooleanAlgebra κ)))))
            (@HeytingAlgebra.toOrderBot (Set κ)
              (@Order.Frame.toHeytingAlgebra (Set κ)
                (@CompleteDistribLattice.toFrame (Set κ)
                  (@CompleteBooleanAlgebra.toCompleteDistribLattice (Set κ)
                    (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra (Set κ)
                      (@Set.instCompleteAtomicBooleanAlgebra κ)))))))
          S) →
      @ProbabilityTheory.iIndepSets Ω ι mΩ (fun i => @piiUnionInter Ω κ π (S i)) μ := by sorry
