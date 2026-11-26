-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_subgroupOf_injective_of_pretransitive
-- name    : SharpIntermediateSubgroupBounds.subgroupOf_injective_of_pretransitive
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:49:53.038804+00:00
-- url     : https://prove2.me/theorems/68905c9a-7907-5c8c-8d47-88d39253b9d0
-- title:
--   Sharp Intermediate Subgroup Bounds: subgroup Of injective of pretransitive
-- statement:
--   A subgroup containing `H` is determined by its intersection with a subgroup acting
--   transitively on `G/H`.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L492-L532
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L492-L532

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

theorem SharpIntermediateSubgroupBounds.subgroupOf_injective_of_pretransitive {P H : Subgroup G}
    (hpre : MulAction.IsPretransitive P (G ⧸ H)) :
    Set.InjOn (fun K : Subgroup G ↦ K.subgroupOf P) (Set.Ici H) := by sorry
