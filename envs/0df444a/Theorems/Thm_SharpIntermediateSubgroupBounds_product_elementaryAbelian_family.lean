-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_product_elementaryAbelian_family
-- name    : SharpIntermediateSubgroupBounds.product_elementaryAbelian_family
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:50:15.599019+00:00
-- url     : https://prove2.me/theorems/f8bef6bb-6eac-43b9-855b-8d9425d74013
-- title:
--   Sharp Intermediate Subgroup Bounds: product elementary Abelian family
-- statement:
--   Index and exact interval count for the full fixed-factor product
--   sharpness family, packaged in one statement.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L817-L827
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L817-L827

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

theorem SharpIntermediateSubgroupBounds.product_elementaryAbelian_family
    (H₀ : Type u) [Group H₀] [Fintype H₀]
    (p a : ℕ) [Fact p.Prime] :
    ((⊤ : Subgroup H₀).prod
      (⊥ : Subgroup (Multiplicative (Fin a → ZMod p)))).index = p ^ a ∧
      Fintype.card
          (Set.Ici ((⊤ : Subgroup H₀).prod
            (⊥ : Subgroup (Multiplicative (Fin a → ZMod p))))) =
        totalQBinom p a := by sorry
