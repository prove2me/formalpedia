-- Prove2me | Theorems.Thm_ThreeSum_LocalCoverMatrix_entry_eq_one_iff
-- name    : ThreeSum.LocalCoverMatrix.entry_eq_one_iff
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:18:48.190095+00:00
-- url     : https://prove2.me/theorems/730170c5-7d1e-42c9-9d94-f9743a3c486e
-- title:
--   The executable cover-matrix bit equals the retained-edge predicate
-- statement:
--   Let $h,L,k,B\in\mathbb N$, let $p$ be the prescribed local prime for $h$, and let $w:[L]\times\{0,1\}\to\mathbb F_p$ assign coordinate-symbol weights. Hash a binary word by summing its selected weights. The local graph has ordered pairs of disjoint $k$-subsets of $[L]$ as edges; its left word is the first subset's indicator and its right word is the complement indicator of the second. Retain only endpoint hash buckets of size at most $B$. For natural $a,b<p$,
--
--   $$
--   \operatorname{entry}(w,k,B,ap+b)=1
--   \iff \operatorname{Covers}(L,k,B,w,(a,b)).
--   $$
--
--   The right side means that at least one retained edge hashes to $(a,b)$, interpreting the targets in $\mathbb F_p$. The left side is the support bit constructed by enumerating subset pairs, checking disjointness and bucket bounds, and marking their packed hash key.
--
--   This identifies the implemented matrix with the finite cover relation.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LocalCoverMatrix.lean#L80-L134

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_LocalMaskHashes_indexed_bucket_count
import Theorems.Thm_ThreeSum_MaskErase_eraseMask_maskOf
import Theorems.Thm_ThreeSum_OneHotMask_eval_maskOf


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.CyclicFold
end ThreeSum.CyclicFold
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.LayerCounts
end ThreeSum.LayerCounts
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.LocalMaskGraph
end ThreeSum.LocalMaskGraph
namespace ThreeSum.LocalMaskHashes
end ThreeSum.LocalMaskHashes
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

theorem ThreeSum.LocalCoverMatrix.entry_eq_one_iff : ∀ {h L k : Nat} (w : ThreeSum.LocalHashMoments.Weight.{0} L (ThreeSum.LocalHashMoments.LocalField h)) {B a b : Nat}
  (ha : @LT.lt.{0} Nat instLTNat a (ThreeSum.LocalCoverBounds.localPrime h))
  (hb : @LT.lt.{0} Nat instLTNat b (ThreeSum.LocalCoverBounds.localPrime h)),
  Iff
    (@Eq.{1} Nat
      (@ThreeSum.LocalCoverMatrix.entry h L w k B
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) a (ThreeSum.LocalCoverBounds.localPrime h))
          b))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@ThreeSum.LocalHashMoments.Covers.{0} (ThreeSum.LocalHashMoments.LocalField h)
      (@ZMod.instField (ThreeSum.LocalCoverBounds.localPrime h) (ThreeSum.LocalHashMoments.localPrimeFact h))
      (@ZMod.fintype (ThreeSum.LocalCoverBounds.localPrime h)
        (@NeZero.of_gt'.{0} Nat (ThreeSum.LocalCoverBounds.localPrime h)
          (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) Nat.instPreorder
          (@LinearOrderedCommMonoidWithZero.toIsBotZeroClass.{0} Nat Nat.instLinearOrderedCommMonoidWithZero)
          Nat.instOne
          (@Nat.Prime.one_lt' (ThreeSum.LocalCoverBounds.localPrime h) (ThreeSum.LocalHashMoments.localPrimeFact h))))
      (ZMod.decidableEq (ThreeSum.LocalCoverBounds.localPrime h)) L k B w
      (@Prod.mk.{0, 0} (ThreeSum.LocalHashMoments.LocalField h) (ThreeSum.LocalHashMoments.LocalField h)
        (@Nat.cast.{0} (ThreeSum.LocalHashMoments.LocalField h)
          (@AddMonoidWithOne.toNatCast.{0} (ThreeSum.LocalHashMoments.LocalField h)
            (@AddGroupWithOne.toAddMonoidWithOne.{0} (ThreeSum.LocalHashMoments.LocalField h)
              (@Ring.toAddGroupWithOne.{0} (ThreeSum.LocalHashMoments.LocalField h)
                (@DivisionRing.toRing.{0} (ThreeSum.LocalHashMoments.LocalField h)
                  (@Field.toDivisionRing.{0} (ThreeSum.LocalHashMoments.LocalField h)
                    (@ZMod.instField (ThreeSum.LocalCoverBounds.localPrime h)
                      (ThreeSum.LocalHashMoments.localPrimeFact h)))))))
          a)
        (@Nat.cast.{0} (ThreeSum.LocalHashMoments.LocalField h)
          (@AddMonoidWithOne.toNatCast.{0} (ThreeSum.LocalHashMoments.LocalField h)
            (@AddGroupWithOne.toAddMonoidWithOne.{0} (ThreeSum.LocalHashMoments.LocalField h)
              (@Ring.toAddGroupWithOne.{0} (ThreeSum.LocalHashMoments.LocalField h)
                (@DivisionRing.toRing.{0} (ThreeSum.LocalHashMoments.LocalField h)
                  (@Field.toDivisionRing.{0} (ThreeSum.LocalHashMoments.LocalField h)
                    (@ZMod.instField (ThreeSum.LocalCoverBounds.localPrime h)
                      (ThreeSum.LocalHashMoments.localPrimeFact h)))))))
          b))) := by
  sorry
