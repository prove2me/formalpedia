-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_normal_of_index_eq_prime_of_isPGroup
-- name    : SharpIntermediateSubgroupBounds.normal_of_index_eq_prime_of_isPGroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:49:43.823844+00:00
-- url     : https://prove2.me/theorems/151990e8-b271-5977-9e3f-799a5206538f
-- title:
--   Sharp Intermediate Subgroup Bounds: normal of index eq prime of is PGroup
-- statement:
--   In a finite `p`-group, a subgroup of index `p` is normal.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L49-L60
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L49-L60

import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Order.Atoms
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Pointwise
noncomputable section
variable {G : Type*} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupCarrierFintype
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupIntervalFintype

theorem SharpIntermediateSubgroupBounds.normal_of_index_eq_prime_of_isPGroup {p : ℕ} (hp : p.Prime)
    (hG : IsPGroup p G) (H : Subgroup G) (hindex : H.index = p) : H.Normal := by sorry
