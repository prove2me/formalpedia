-- Prove2me | Theorems.Thm_ThreeSum_MaskDifference_subsetMask_union_sdiff
-- name    : ThreeSum.MaskDifference.subsetMask_union_sdiff
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T06:43:01.222058+00:00
-- url     : https://prove2.me/theorems/589fe215-a739-42a5-87d1-1a05080c76d4
-- title:
--   Disjoint subset masks add without carries
-- statement:
--   Let $L\in\mathbb N$ and let $U\subseteq Q\subseteq\{0,\ldots,L-1\}$. Encode a subset by its binary mask $M(S)=\sum_{i\in S}2^i$. Then
--
--   $$M(U)+M(Q\setminus U)=M(Q).$$
--
--   This arithmetic identity implements the decomposition of a query set into a selected subset and its complement within the query.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/MaskDifference.lean#L24-L44

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

theorem ThreeSum.MaskDifference.subsetMask_union_sdiff : ∀ {L : Nat} (Q U : Finset.{0} (Fin L))
  (hU :
    @LE.le.{0} (Finset.{0} (Fin L))
      (@Preorder.toLE.{0} (Finset.{0} (Fin L))
        (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin L)) (@Finset.instPartialOrder.{0} (Fin L))))
      U Q),
  @Eq.{1} Nat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@ThreeSum.SubsetAddress.subsetMask L U)
      (@ThreeSum.SubsetAddress.subsetMask L
        (@SDiff.sdiff.{0} (Finset.{0} (Fin L)) (@Finset.instSDiff.{0} (Fin L) (instDecidableEqFin L)) Q U)))
    (@ThreeSum.SubsetAddress.subsetMask L Q) := by
  sorry
