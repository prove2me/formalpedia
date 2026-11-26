-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_leaf_product_bound_sameUniverse
-- name    : SharpIntermediateSubgroupBounds.BranchingTree.leaf_product_bound_sameUniverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:44:10.059457+00:00
-- url     : https://prove2.me/theorems/15e64532-8c03-5f7d-939a-7436d2a638a9
-- title:
--   Branching Tree: leaf product bound same Universe
-- statement:
--   Same-universe wrapper for applications in which states and choices are
--   subtypes of one fixed ambient type.  Making this universe equality explicit
--   avoids leaving a metavariable in downstream declarations.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Tree.lean#L104-L111
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Tree.lean#L104-L111

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

theorem SharpIntermediateSubgroupBounds.BranchingTree.leaf_product_bound_sameUniverse {State : Type u}
    (Choice : State → Type u) [∀ s, Fintype (Choice s)]
    (next : ∀ s, Choice s → State) [∀ s, Nonempty (Choice s)]
    (r : ℕ) (s : State) (q : ℚ)
    (hq : ∀ z : Path Choice next r s,
      q ≤ (branchProduct Choice next z : ℚ)) :
    q ≤ (Fintype.card (Path Choice next r s) : ℚ) := by sorry
