-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_gammaQ_antitone
-- name    : SharpIntermediateSubgroupBounds.gammaQ_antitone
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:45:01.110976+00:00
-- url     : https://prove2.me/theorems/9ac5025b-30ec-4535-bb58-305e11cbafcb
-- title:
--   Sharp Intermediate Subgroup Bounds: gamma Q antitone
-- statement:
--   The finite Euler products are antitone in the length.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean#L428-L430
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean#L428-L430

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

theorem SharpIntermediateSubgroupBounds.gammaQ_antitone {p : ℕ} (hp : 1 < p) :
    Antitone (gammaQ p) := by sorry
