-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_gammaQ_mono_base
-- name    : SharpIntermediateSubgroupBounds.gammaQ_mono_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:42:42.084845+00:00
-- url     : https://prove2.me/theorems/e28bc340-50e5-5b6d-b221-19c21dd8cddf
-- title:
--   Sharp Intermediate Subgroup Bounds: gamma Q mono base
-- statement:
--   For fixed length the Euler factor increases with its base.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean#L433-L448
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean#L433-L448

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

theorem SharpIntermediateSubgroupBounds.gammaQ_mono_base {q p r : ℕ} (hq : 1 < q) (hqp : q ≤ p) :
    gammaQ q r ≤ gammaQ p r := by sorry
