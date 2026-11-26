-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_leaf_product_bound
-- name    : SharpIntermediateSubgroupBounds.BranchingTree.leaf_product_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:44:13.028949+00:00
-- url     : https://prove2.me/theorems/a9293bdd-a63d-4f66-92fb-73723edc0404
-- title:
--   Branching Tree: leaf product bound
-- statement:
--   The leaf-product bound.  Positivity of every branching type is the
--   type-theoretic form of saying that no leaf occurs before the prescribed
--   depth.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Tree.lean#L63-L99
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Tree.lean#L63-L99

import Definitions.Def_SharpIntermediateSubgroupBounds_Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_SharpIntermediateSubgroupBounds_Tree
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
open SharpIntermediateSubgroupBounds.BranchingTree
universe u
variable {State : Type*}
variable (Choice : State → Type*) [∀ s, Fintype (Choice s)]
variable (next : ∀ s, Choice s → State)

theorem SharpIntermediateSubgroupBounds.BranchingTree.leaf_product_bound [∀ s, Nonempty (Choice s)]
    (r : ℕ) (s : State) (q : ℚ)
    (hq : ∀ z : Path Choice next r s,
      q ≤ (branchProduct Choice next z : ℚ)) :
    q ≤ (Fintype.card (Path Choice next r s) : ℚ) := by sorry
