-- Prove2me | Theorems.Thm_ThreeSum_SparseBoxes_mem_explicitLeaves
-- name    : ThreeSum.SparseBoxes.mem_explicitLeaves
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:26:46.477168+00:00
-- url     : https://prove2.me/theorems/c17234b2-bc50-48d8-bf3f-9c9674475308
-- title:
--   Membership in the explicit-leaf family
-- statement:
--   Let $q,\ell$ be finite subsets of a linearly ordered type and let $t\in\mathbb N$. Define the explicit-leaf family by taking $q\setminus m$ for every missing set $m\subseteq q$ of size less than $t$. Then
--
--   $$
--   \ell\in\operatorname{explicitLeaves}(q,t)\quad\Longleftrightarrow\quad\ell\subseteq q\ \land\ |q\setminus\ell|<t.
--   $$
--
--   This characterizes precisely the leaves handled by direct accesses in the sparse-query decomposition, including the empty family at threshold zero.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SparseBoxes.lean#L549-L564

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Push


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1

theorem ThreeSum.SparseBoxes.mem_explicitLeaves : ∀ {α : Type u_1} [inst : LinearOrder.{u_1} α] (q leaf : Finset.{u_1} α) (t : Nat),
  Iff
    (@Membership.mem.{u_1, u_1} (Finset.{u_1} α) (Finset.{u_1} (Finset.{u_1} α))
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} (Finset.{u_1} α)) (Finset.{u_1} α)
        (@Finset.instSetLike.{u_1} (Finset.{u_1} α)))
      (@ThreeSum.SparseBoxes.explicitLeaves.{u_1} α inst q t) leaf)
    (And
      (@LE.le.{u_1} (Finset.{u_1} α)
        (@Preorder.toLE.{u_1} (Finset.{u_1} α)
          (@PartialOrder.toPreorder.{u_1} (Finset.{u_1} α) (@Finset.instPartialOrder.{u_1} α)))
        leaf q)
      (@LT.lt.{0} Nat instLTNat
        (@Finset.card.{u_1} α
          (@SDiff.sdiff.{u_1} (Finset.{u_1} α)
            (@Finset.instSDiff.{u_1} α fun (a b : α) => @LinearOrder.toDecidableEq.{u_1} α inst a b) q leaf))
        t)) := by
  sorry
