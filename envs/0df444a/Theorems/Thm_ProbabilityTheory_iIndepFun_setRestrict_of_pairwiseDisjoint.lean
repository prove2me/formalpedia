-- Prove2me | Theorems.Thm_ProbabilityTheory_iIndepFun_setRestrict_of_pairwiseDisjoint
-- name    : ProbabilityTheory.iIndepFun.setRestrict_of_pairwiseDisjoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:54:50.729605+00:00
-- url     : https://prove2.me/theorems/53e58ea0-2b57-4356-8a18-465643076cc7
-- title:
--   LeanLevy: ProbabilityTheory.iIndepFun.setRestrict_of_pairwiseDisjoint
-- statement:
--   Blocks of a mutually independent family of random variables, grouped along Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Probability/IndependenceGrouping.lean#L134

import Definitions.Def_LeanLevy_Probability_IndependenceGrouping
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.PiSystem

universe u_1 u_2 u_3 u_4
theorem ProbabilityTheory.iIndepFun.setRestrict_of_pairwiseDisjoint : ∀ {Ω : Type u_1} {ι : Type u_2} {κ : Type u_3} {mΩ : MeasurableSpace Ω} {μ : @MeasureTheory.Measure Ω mΩ}
  {β : κ → Type u_4} {mβ : (k : κ) → MeasurableSpace (β k)} {f : (k : κ) → Ω → β k},
  (∀ (k : κ), @Measurable Ω (β k) mΩ (mβ k) (f k)) →
    @ProbabilityTheory.iIndepFun Ω κ mΩ β mβ f μ →
      ∀ {S : ι → Set κ},
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
          @ProbabilityTheory.iIndepFun Ω ι mΩ
            (fun i =>
              (a : @Set.Elem κ (S i)) →
                β (@Subtype.val κ (fun x => @Membership.mem κ (Set κ) (@Set.instMembership κ) (S i) x) a))
            (fun x =>
              @MeasurableSpace.pi (@Set.Elem κ (S x))
                (fun a => β (@Subtype.val κ (fun x_1 => @Membership.mem κ (Set κ) (@Set.instMembership κ) (S x) x_1) a))
                fun a => mβ (@Subtype.val κ (fun x_1 => @Membership.mem κ (Set κ) (@Set.instMembership κ) (S x) x_1) a))
            (fun i ω => @Set.restrict κ β (S i) fun k => f k ω) μ := by sorry
