-- Prove2me | Theorems.Thm_ThreeSum_LocalMaskHashes_indexed_bucket_count
-- name    : ThreeSum.LocalMaskHashes.indexed_bucket_count
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:47:19.478985+00:00
-- url     : https://prove2.me/theorems/7544715f-1a7d-425d-aa33-6f5b9e2a2ed7
-- title:
--   A histogram over mask indices counts the abstract hash bucket
-- statement:
--   Let $p_h$ be the local prime, $w$ a one-hot coefficient function over $\mathbb F_{p_h}$ on $L$ Boolean coordinates, and $S_0,\ldots,S_{V-1}$ the exact enumeration of all $k$-element subsets, where $V=\binom Lk$. Let $\phi$ be an injective map from subsets to Boolean words. Suppose natural codes satisfy $c_i<p_h$ and represent $H_w(\phi(S_i))$ in the field for every $i<V$. For $r<p_h$,
--
--   $$|\{i<V:c_i=r\}|=|\{\phi(S):|S|=k,\ H_w(\phi(S))=r\}|.$$
--
--   This identifies the concrete indexed histogram with the semantic bucket cardinality, with canonical residue bounds preventing numerical aliases.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LocalMaskHashes.lean#L71-L101

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
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
import Theorems.Thm_ThreeSum_SubsetAddress_enumerateLayer_nodup


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.LocalMaskGraph
end ThreeSum.LocalMaskGraph
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

theorem ThreeSum.LocalMaskHashes.indexed_bucket_count : ∀ {h L k : Nat} (w : ThreeSum.LocalHashMoments.Weight.{0} L (ThreeSum.LocalHashMoments.LocalField h))
  (shape : Finset.{0} (Fin L) → Fin L → Bool)
  (hinj : @Function.Injective.{1, 1} (Finset.{0} (Fin L)) (Fin L → Bool) shape) (code : Nat → Nat)
  (hcodeLt :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i (ThreeSum.LocalMaskGraph.vertexCount L k) →
        @LT.lt.{0} Nat instLTNat (code i) (ThreeSum.LocalCoverBounds.localPrime h))
  (hcode :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i (ThreeSum.LocalMaskGraph.vertexCount L k) →
        @Eq.{1} (ThreeSum.LocalHashMoments.LocalField h)
          (@Nat.cast.{0} (ThreeSum.LocalHashMoments.LocalField h)
            (@AddMonoidWithOne.toNatCast.{0} (ThreeSum.LocalHashMoments.LocalField h)
              (@AddGroupWithOne.toAddMonoidWithOne.{0} (ThreeSum.LocalHashMoments.LocalField h)
                (@Ring.toAddGroupWithOne.{0} (ThreeSum.LocalHashMoments.LocalField h)
                  (@DivisionRing.toRing.{0} (ThreeSum.LocalHashMoments.LocalField h)
                    (@Field.toDivisionRing.{0} (ThreeSum.LocalHashMoments.LocalField h)
                      (@ZMod.instField (ThreeSum.LocalCoverBounds.localPrime h)
                        (ThreeSum.LocalHashMoments.localPrimeFact h)))))))
            (code i))
          (@ThreeSum.HashFamily.hashValue.{0, 0} (Fin L) (ThreeSum.LocalHashMoments.LocalField h) (Fin.fintype L)
            (@ZMod.instField (ThreeSum.LocalCoverBounds.localPrime h) (ThreeSum.LocalHashMoments.localPrimeFact h)) w
            (shape (ThreeSum.LocalMaskGraph.setAt L k i))))
  {r : Nat} (hr : @LT.lt.{0} Nat instLTNat r (ThreeSum.LocalCoverBounds.localPrime h)),
  @Eq.{1} Nat (ThreeSum.LightHistogram.count code r (ThreeSum.LocalMaskGraph.vertexCount L k))
    (@ThreeSum.HashFamily.bucketSize.{0, 0} (Fin L) (ThreeSum.LocalHashMoments.LocalField h) (Fin.fintype L)
      (@ZMod.instField (ThreeSum.LocalCoverBounds.localPrime h) (ThreeSum.LocalHashMoments.localPrimeFact h))
      (ZMod.decidableEq (ThreeSum.LocalCoverBounds.localPrime h))
      (@Finset.image.{0, 0} (Finset.{0} (Fin L)) (Fin L → Bool)
        (fun (a b : Fin L → Bool) =>
          @Fintype.decidablePiFintype.{0, 0} (Fin L) (fun (a : Fin L) => Bool) (fun (a : Fin L) => instDecidableEqBool)
            (Fin.fintype L) a b)
        shape (ThreeSum.LayerCounts.vertices L k))
      w
      (@Nat.cast.{0} (ThreeSum.LocalHashMoments.LocalField h)
        (@AddMonoidWithOne.toNatCast.{0} (ThreeSum.LocalHashMoments.LocalField h)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} (ThreeSum.LocalHashMoments.LocalField h)
            (@Ring.toAddGroupWithOne.{0} (ThreeSum.LocalHashMoments.LocalField h)
              (@DivisionRing.toRing.{0} (ThreeSum.LocalHashMoments.LocalField h)
                (@Field.toDivisionRing.{0} (ThreeSum.LocalHashMoments.LocalField h)
                  (@ZMod.instField (ThreeSum.LocalCoverBounds.localPrime h)
                    (ThreeSum.LocalHashMoments.localPrimeFact h)))))))
        r)) := by
  sorry
