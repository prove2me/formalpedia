-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_product_elementaryAbelian_index_eq
-- name    : SharpIntermediateSubgroupBounds.product_elementaryAbelian_index_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:50:10.383869+00:00
-- url     : https://prove2.me/theorems/633072ad-3dcd-55c3-86dd-ce81d0ba738d
-- title:
--   Sharp Intermediate Subgroup Bounds: product elementary Abelian index eq
-- statement:
--   The index of the literal product inclusion is the order of its
--   elementary-abelian second factor.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L804-L813
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L804-L813

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
universe u v

theorem SharpIntermediateSubgroupBounds.product_elementaryAbelian_index_eq
    (H₀ : Type u) [Group H₀] [Fintype H₀]
    (p a : ℕ) [Fact p.Prime] :
    ((⊤ : Subgroup H₀).prod
      (⊥ : Subgroup (Multiplicative (Fin a → ZMod p)))).index = p ^ a := by sorry
