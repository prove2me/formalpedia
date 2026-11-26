-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_escape_path_branchProduct_bound
-- name    : SharpIntermediateSubgroupBounds.escape_path_branchProduct_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:45:05.934954+00:00
-- url     : https://prove2.me/theorems/593f2ea6-faf3-446e-b082-2471e6a1ad35
-- title:
--   Sharp Intermediate Subgroup Bounds: escape path branch Product bound
-- statement:
--   Pathwise lower bound for the product of the escape-tree branching
--   degrees.  The exponent in `gammaQ` records exactly the strict moves made
--   along the path.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean#L724-L820
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean#L724-L820

import Definitions.Def_SharpIntermediateSubgroupBounds_Tree
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupDecidableEq

theorem SharpIntermediateSubgroupBounds.escape_path_branchProduct_bound {H K : Subgroup G}
    (hn : 1 < H.index) (hHK : H ≤ K) {r : ℕ}
    {s : EscapeState K} (hHs : H ≤ s.1) (z : EscapePath K r s) :
    gammaQ H.index.minFac (escapeStrictCount K z) *
        (Nat.card K : ℚ) ^ r ≤
      (BranchingTree.branchProduct (EscapeChoice K) (escapeNext K) z : ℚ) := by sorry
