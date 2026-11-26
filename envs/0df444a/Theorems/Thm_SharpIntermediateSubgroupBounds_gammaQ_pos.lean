-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_gammaQ_pos
-- name    : SharpIntermediateSubgroupBounds.gammaQ_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:42:38.967925+00:00
-- url     : https://prove2.me/theorems/63e41716-47bc-4fb9-90c5-6186327230d2
-- title:
--   Sharp Intermediate Subgroup Bounds: gamma Q pos
-- statement:
--   The finite Euler factor is strictly positive for every base at least
--   two.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean#L411-L418
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean#L411-L418

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

theorem SharpIntermediateSubgroupBounds.gammaQ_pos {p r : ℕ} (hp : 1 < p) : 0 < gammaQ p r := by sorry
