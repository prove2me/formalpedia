-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_elementarySubgroup_index_eq_pow_of_finrank
-- name    : SharpIntermediateSubgroupBounds.elementarySubgroup_index_eq_pow_of_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:50:12.415967+00:00
-- url     : https://prove2.me/theorems/507dd565-b136-4100-97ee-de8034369c92
-- title:
--   Sharp Intermediate Subgroup Bounds: elementary Subgroup index eq pow of finrank
-- statement:
--   Index `p^k` is equivalent to codimension `k`, reverse direction.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L663-L677
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L663-L677

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

theorem SharpIntermediateSubgroupBounds.elementarySubgroup_index_eq_pow_of_finrank {p a k : ℕ} [Fact p.Prime]
    (hk : k ≤ a) (Q : Subgroup (Multiplicative (Fin a → ZMod p)))
    (hrank : Module.finrank (ZMod p) (elementarySubgroupSubmoduleIso p a Q) = a - k) :
    Q.index = p ^ k := by sorry
