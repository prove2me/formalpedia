-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_elementarySubgroup_finrank_eq_sub_of_index
-- name    : SharpIntermediateSubgroupBounds.elementarySubgroup_finrank_eq_sub_of_index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:50:10.528536+00:00
-- url     : https://prove2.me/theorems/ec2e2211-1890-4dbf-9735-98637374af7a
-- title:
--   Sharp Intermediate Subgroup Bounds: elementary Subgroup finrank eq sub of index
-- statement:
--   Index `p^k` is equivalent to codimension `k`, forward direction.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L645-L660
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L645-L660

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
attribute [local instance] SharpIntermediateSubgroupBounds.coatomFiberFintype

theorem SharpIntermediateSubgroupBounds.elementarySubgroup_finrank_eq_sub_of_index {p a k : ℕ} [Fact p.Prime]
    (hk : k ≤ a) (Q : Subgroup (Multiplicative (Fin a → ZMod p)))
    (hindex : Q.index = p ^ k) :
    Module.finrank (ZMod p) (elementarySubgroupSubmoduleIso p a Q) = a - k := by sorry
