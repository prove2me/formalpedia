-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_elementaryAbelian_interval_card_eq_totalQBinom
-- name    : SharpIntermediateSubgroupBounds.elementaryAbelian_interval_card_eq_totalQBinom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:43:48.294068+00:00
-- url     : https://prove2.me/theorems/32937140-2c0a-539b-af6c-7a0f7ed49282
-- title:
--   Sharp Intermediate Subgroup Bounds: elementary Abelian interval card eq total QBinom
-- statement:
--   Elementary abelian groups attain the bound.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L723-L745
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L723-L745

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

theorem SharpIntermediateSubgroupBounds.elementaryAbelian_interval_card_eq_totalQBinom (p a : ℕ) [Fact p.Prime] :
    Fintype.card
        (Set.Ici (⊥ : Subgroup (Multiplicative (Fin a → ZMod p)))) = totalQBinom p a := by sorry
