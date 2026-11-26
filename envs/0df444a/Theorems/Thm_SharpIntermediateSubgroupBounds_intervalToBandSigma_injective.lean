-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_intervalToBandSigma_injective
-- name    : SharpIntermediateSubgroupBounds.intervalToBandSigma_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:45:30.673143+00:00
-- url     : https://prove2.me/theorems/3289cf99-7efe-5e77-a254-d0c85a43c27f
-- title:
--   Sharp Intermediate Subgroup Bounds: interval To Band Sigma injective
-- statement:
--   The Sharp Intermediate Subgroup Bounds construction uses the interval To Band Sigma injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L297-L302
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L297-L302

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

theorem SharpIntermediateSubgroupBounds.intervalToBandSigma_injective (H : Subgroup G) (q : ℕ)
    (hn : 1 < H.index) (hq : 1 < q) :
    Function.Injective (intervalToBandSigma H q hn hq) := by sorry
