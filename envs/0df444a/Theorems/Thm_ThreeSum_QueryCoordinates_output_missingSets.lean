-- Prove2me | Theorems.Thm_ThreeSum_QueryCoordinates_output_missingSets
-- name    : ThreeSum.QueryCoordinates.output_missingSets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:25:54.741029+00:00
-- url     : https://prove2.me/theorems/086b4b80-5060-4ed5-9ab0-47fac4a93985
-- title:
--   Weighted enumeration returns the exact missing-subset mask list
-- statement:
--   Let $W,k\in\mathbb N$ and $Q\subseteq\{0,\ldots,W-1\}$. List the elements of $Q$ in increasing order and assign the weight $2^a$ to coordinate $a$. Let $\mathcal M_k(Q)$ be the canonical list of $k$-element subsets obtained from fixed-length sublists of the reversed coordinate list. The weighted enumerator, with $|Q|$ weights and initial offset zero, returns exactly
--
--   $$
--   \operatorname{output}(w_Q,|Q|,k,0)=\left[\sum_{a\in S}2^a\ :\ S\text{ in }\mathcal M_k(Q)\right].
--   $$
--
--   The equality is of ordered integer lists, with the subset masks cast from natural numbers. It supplies the exact list semantics required by the query-coordinate implementation.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/QueryCoordinates.lean#L235-L256

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightSubsetEnumeration
end ThreeSum.LightSubsetEnumeration
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

theorem ThreeSum.QueryCoordinates.output_missingSets : ∀ {W : Nat} (Q : Finset.{0} (Fin W)) (k : Nat),
  @Eq.{1} (List.{0} Int)
    (ThreeSum.LightWeightedEnumeration.output (@ThreeSum.QueryCoordinates.weights W Q) (@Finset.card.{0} (Fin W) Q) k
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@List.map.{0, 0} Nat Int (@Nat.cast.{0} Int instNatCastInt)
      (@List.map.{0, 0} (Finset.{0} (Fin W)) Nat (@ThreeSum.SubsetAddress.subsetMask W)
        (@ThreeSum.QueryCoordinates.missingSets W Q k))) := by
  sorry
