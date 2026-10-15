-- Prove2me | Theorems.Thm_ThreeSum_BlockForced_transformPrefixValue_eq_bucket_sum
-- name    : ThreeSum.BlockForced.transformPrefixValue_eq_bucket_sum
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:32:48.330985+00:00
-- url     : https://prove2.me/theorems/5cdea74a-48c3-463e-a2f8-9d948be6218c
-- title:
--   Forced-prefix subset transforms count completed bucket pairs
-- statement:
--   Fix natural $h,J$, integers $P,d$, finite indexed sets $B,C$ in finite types with decidable equality, and integer values $b,c$. Let $q$ specify the map occurrence and $2h$-element output row in every block. For any set $I$ of forced blocks, choose $h$-element subsets $u_i\subseteq q_i$, $i\in I$.
--
--   Let $P_L$ join these subsets, $P_R$ join their complements in the forced output rows, $D$ be the full unforced coordinate domain, and $R$ the unforced output rows. Let $F,G$ be the concrete independently trimmed left and right original-input bucket-weight functions. With partial subset-zeta transform $Z_D$ and subset Möbius transform $\mathcal M$,
--   $$
--   \mathcal M\!\left(z\mapsto Z_DF(P_L\cup z)Z_DG(P_R\cup z)\right)(R)
--   =\sum_{t\in\mathcal C(q,I,u)}L_tR_t.
--   $$
--   Here $\mathcal C$ consists of retained tuples completing the forced rows, and $L_t,R_t$ are their original-index bucket counts for $b\bmod P$ and $c\bmod P+d$.
--
--   This gives the exact bucket-count meaning of the stored forced-prefix transform.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BlockForced.lean#L265-L288

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.NumberTheory.Bertrand
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_BlockForced_completed_bucket_sum
import Theorems.Thm_ThreeSum_Subset_forced_prefix_identity


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting

universe u_1 u_2

theorem ThreeSum.BlockForced.transformPrefixValue_eq_bucket_sum : ∀ {β : Type u_1} {γ : Type u_2} [Fintype.{u_1} β] [Fintype.{u_2} γ] [DecidableEq.{u_1 + 1} β] [DecidableEq.{u_2 + 1} γ]
  {h J : Nat} (P d : Int) (B : Finset.{u_1} β) (C : Finset.{u_2} γ) (b : β → Int) (c : γ → Int)
  (q : ThreeSum.GlobalEncoding.GlobalOutput h J) (I : Finset.{0} (Fin J))
  (u :
    Fin J →
      Finset.{0}
        (Fin
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
  (hu :
    ∀ (i : Fin J),
      @Membership.mem.{0, 0} (Fin J) (Finset.{0} (Fin J))
          (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin J)) (Fin J) (@Finset.instSetLike.{0} (Fin J))) I i →
        And
          (@LE.le.{0}
            (Finset.{0}
              (Fin
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
            (@Preorder.toLE.{0}
              (Finset.{0}
                (Fin
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
              (@PartialOrder.toPreorder.{0}
                (Finset.{0}
                  (Fin
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
                (@Finset.instPartialOrder.{0}
                  (Fin
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))))
            (u i) (@ThreeSum.BlockForced.outputRows h J q i))
          (@Eq.{1} Nat
            (@Finset.card.{0}
              (Fin
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
              (u i))
            h)),
  @Eq.{1} Int (@ThreeSum.BlockForced.transformPrefixValue.{u_1, u_2} β γ h J P d B C b c q I u)
    (@Nat.cast.{0} Int instNatCastInt
      (∑ t ∈ @ThreeSum.BlockForced.completedTuples h J q I u,
        @HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@ThreeSum.RawIncidences.leftBucket.{u_1} β h J P B b t)
          (@ThreeSum.RawIncidences.rightBucket.{u_2} γ h J P d C c t))) := by
  sorry
