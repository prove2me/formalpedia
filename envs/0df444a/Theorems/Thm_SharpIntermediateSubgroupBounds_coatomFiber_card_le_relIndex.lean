-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_coatomFiber_card_le_relIndex
-- name    : SharpIntermediateSubgroupBounds.coatomFiber_card_le_relIndex
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:49:51.682197+00:00
-- url     : https://prove2.me/theorems/ea1f0a81-9e1c-4ff7-af40-4f0a97211e64
-- title:
--   Sharp Intermediate Subgroup Bounds: coatom Fiber card le rel Index
-- statement:
--   All subgroups with a fixed intersection with a normal coatom inject into the corresponding
--   coset space.  Notice that this statement does not require a `p`-group hypothesis.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L71-L157
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L71-L157

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

theorem SharpIntermediateSubgroupBounds.coatomFiber_card_le_relIndex (M V : Subgroup G) [M.Normal]
    (hM : IsCoatom M) (hVM : V ≤ M) :
    Fintype.card (CoatomFiber M V) ≤ V.relIndex M := by sorry
