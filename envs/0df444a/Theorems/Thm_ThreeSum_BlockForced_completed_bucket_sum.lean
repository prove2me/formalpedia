-- Prove2me | Theorems.Thm_ThreeSum_BlockForced_completed_bucket_sum
-- name    : ThreeSum.BlockForced.completed_bucket_sum
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:41:59.655404+00:00
-- url     : https://prove2.me/theorems/67aa6c07-a33a-448e-95d4-f564df29c89f
-- title:
--   Completed bucket counts equal the forced-prefix subset sum
-- statement:
--   Let $h,J\in\mathbb N$, let $q$ be a global output with occurrence vector $o$ and local output sets $Q_i$, and fix completed blocks $I$ with subsets $u_i\subseteq Q_i$ for $i\in I$. Define $P_L$ from the chosen $u_i$, $P_R$ from $Q_i\setminus u_i$ on those blocks, and $R$ from all output coordinates in the other blocks. Let $B,C$ be finite subsets of finite index types with decidable equality, with integer values $b,c$, modulus parameter $P\in\mathbb Z$, and shift $d\in\mathbb Z$. Write $\mathcal T$ for retained tuples with output $q$ agreeing with $u$ on $I$. Then
--
--   $$
--   \sum_{t\in\mathcal T}\operatorname{bucket}_L(t)\operatorname{bucket}_R(t)
--   =\sum_{X\subseteq R}w_L(P_L\cup X)\,w_R(P_R\cup(R\setminus X)).
--   $$
--
--   The buckets count B/C indices matching the tuple endpoints modulo the global modulus, after remainder modulo $P$ and right shift $d$. The weights perform those counts for a subset endpoint and are zero unless every row has size $h$ and satisfies its independent bucket-cap condition. This converts completed reporting counts into a finite subset query.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BlockForced.lean#L218-L251

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
import Theorems.Thm_ThreeSum_BlockForced_forced_disjoint
import Theorems.Thm_ThreeSum_BlockForced_forced_union


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
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting

universe u_1 u_2

theorem ThreeSum.BlockForced.completed_bucket_sum : ∀ {β : Type u_1} {γ : Type u_2} [Fintype.{u_1} β] [Fintype.{u_2} γ] [DecidableEq.{u_1 + 1} β] [DecidableEq.{u_2 + 1} γ]
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
        @LE.le.{0}
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
          (u i) (@ThreeSum.BlockForced.outputRows h J q i)),
  @Eq.{1} Nat
    (∑ t ∈ @ThreeSum.BlockForced.completedTuples h J q I u,
      @HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@ThreeSum.RawIncidences.leftBucket.{u_1} β h J P B b t)
        (@ThreeSum.RawIncidences.rightBucket.{u_2} γ h J P d C c t))
    (∑
      x ∈
        @Finset.powerset.{0}
          (ThreeSum.BlockRows.Coord J
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
          (@ThreeSum.BlockForced.remaining J
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
            I (@ThreeSum.BlockForced.outputRows h J q)),
      @HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@ThreeSum.BlockEncoding.leftWeights.{u_1} β h J (@ThreeSum.BlockEncoding.outputOccurrences h J q) P B b
          (@Union.union.{0}
            (Finset.{0}
              (ThreeSum.BlockRows.Coord J
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
            (@Finset.instUnion.{0}
              (ThreeSum.BlockRows.Coord J
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
              fun
                (a b :
                  ThreeSum.BlockRows.Coord J
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)) =>
              @Sigma.instDecidableEqSigma.{0, 0} (Fin J)
                (fun (_i : Fin J) =>
                  Fin
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                (instDecidableEqFin J)
                (fun (a : Fin J) =>
                  instDecidableEqFin
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                a b)
            (@ThreeSum.BlockForced.prefixLeft J
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
              I u)
            x))
        (@ThreeSum.BlockEncoding.rightWeights.{u_2} γ h J (@ThreeSum.BlockEncoding.outputOccurrences h J q) P d C c
          (@Union.union.{0}
            (Finset.{0}
              (ThreeSum.BlockRows.Coord J
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
            (@Finset.instUnion.{0}
              (ThreeSum.BlockRows.Coord J
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
              fun
                (a b :
                  ThreeSum.BlockRows.Coord J
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)) =>
              @Sigma.instDecidableEqSigma.{0, 0} (Fin J)
                (fun (_i : Fin J) =>
                  Fin
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                (instDecidableEqFin J)
                (fun (a : Fin J) =>
                  instDecidableEqFin
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                a b)
            (@ThreeSum.BlockForced.prefixRight J
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
              I (@ThreeSum.BlockForced.outputRows h J q) u)
            (@SDiff.sdiff.{0}
              (Finset.{0}
                (ThreeSum.BlockRows.Coord J
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
              (@Finset.instSDiff.{0}
                (ThreeSum.BlockRows.Coord J
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                fun
                  (a b :
                    ThreeSum.BlockRows.Coord J
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)) =>
                @Sigma.instDecidableEqSigma.{0, 0} (Fin J)
                  (fun (_i : Fin J) =>
                    Fin
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                  (instDecidableEqFin J)
                  (fun (a : Fin J) =>
                    instDecidableEqFin
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                  a b)
              (@ThreeSum.BlockForced.remaining J
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                I (@ThreeSum.BlockForced.outputRows h J q))
              x)))) := by
  sorry
