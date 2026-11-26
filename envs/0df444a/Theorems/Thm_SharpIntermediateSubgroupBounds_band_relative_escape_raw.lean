-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_band_relative_escape_raw
-- name    : SharpIntermediateSubgroupBounds.band_relative_escape_raw
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:45:16.125602+00:00
-- url     : https://prove2.me/theorems/06b90637-8984-544d-b318-afc8c5617e6c
-- title:
--   Sharp Intermediate Subgroup Bounds: band relative escape raw
-- statement:
--   Relative escape for one member of a `q`-band, allowing any
--   `2 ≤ q ≤ minFac [G:H]`.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L95-L104
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L95-L104

import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Packing
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.packingSubgroupDecidableEq
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupFinite

theorem SharpIntermediateSubgroupBounds.band_relative_escape_raw {H : Subgroup G} (hn : 1 < H.index)
    {q r : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac)
    (K : band H q r) :
    gammaQ q r * (Nat.card K.1 : ℚ) ^ r ≤
      (Nat.card (RawRelGen H K.1 r) : ℚ) := by sorry
