-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_product_elementaryAbelian_interval_card_eq
-- name    : SharpIntermediateSubgroupBounds.product_elementaryAbelian_interval_card_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:44:06.538741+00:00
-- url     : https://prove2.me/theorems/133491c7-6d89-5e2d-aa49-a35907d54af9
-- title:
--   Sharp Intermediate Subgroup Bounds: product elementary Abelian interval card eq
-- statement:
--   The literal inclusions `H₀ × 1 ≤ H₀ × E` attain the exact
--   prime-power interval bound when `E` is elementary abelian.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L789-L800
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L789-L800

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

theorem SharpIntermediateSubgroupBounds.product_elementaryAbelian_interval_card_eq
    (H₀ : Type u) [Group H₀] [Fintype H₀]
    (p a : ℕ) [Fact p.Prime] :
    Fintype.card
        (Set.Ici ((⊤ : Subgroup H₀).prod
          (⊥ : Subgroup (Multiplicative (Fin a → ZMod p))))) =
      totalQBinom p a := by sorry
