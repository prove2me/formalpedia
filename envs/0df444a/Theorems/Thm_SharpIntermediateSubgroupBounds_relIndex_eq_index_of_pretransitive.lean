-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_relIndex_eq_index_of_pretransitive
-- name    : SharpIntermediateSubgroupBounds.relIndex_eq_index_of_pretransitive
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:49:49.836498+00:00
-- url     : https://prove2.me/theorems/7c051634-c0dd-5096-b4f0-fc23cfc0d420
-- title:
--   Sharp Intermediate Subgroup Bounds: rel Index eq index of pretransitive
-- statement:
--   Under a transitive `P`-action on `G/H`, intersection with `P` preserves all later indices.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L473-L488
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L473-L488

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

theorem SharpIntermediateSubgroupBounds.relIndex_eq_index_of_pretransitive {P H K : Subgroup G}
    (hpre : MulAction.IsPretransitive P (G ⧸ H)) (hHK : H ≤ K) :
    K.relIndex P = K.index := by sorry
