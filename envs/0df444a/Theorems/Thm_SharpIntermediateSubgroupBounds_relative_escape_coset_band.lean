-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_relative_escape_coset_band
-- name    : SharpIntermediateSubgroupBounds.relative_escape_coset_band
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:51:52.558624+00:00
-- url     : https://prove2.me/theorems/6d3a4c0d-3408-45c6-85cf-64f41df71199
-- title:
--   Sharp Intermediate Subgroup Bounds: relative escape coset band
-- statement:
--   The manuscript's band-form statement of Proposition 2.3.  The lower
--   band inequality records that `K` is in band `r`; escape itself uses the
--   upper inequality.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean#L981-L987
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean#L981-L987

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

theorem SharpIntermediateSubgroupBounds.relative_escape_coset_band {H K : Subgroup G}
    (hn : 1 < H.index) (hHK : H ≤ K) {r : ℕ}
    (_hlo : H.index.minFac ^ r ≤ H.relIndex K)
    (hhi : H.relIndex K < H.index.minFac ^ (r + 1)) :
    gammaQ H.index.minFac r * (H.relIndex K : ℚ) ^ r ≤
      (Nat.card (CosetRelGen H K r) : ℚ) := by sorry
