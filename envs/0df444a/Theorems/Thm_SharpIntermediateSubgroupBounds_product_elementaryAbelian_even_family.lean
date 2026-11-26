-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_product_elementaryAbelian_even_family
-- name    : SharpIntermediateSubgroupBounds.product_elementaryAbelian_even_family
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:00:27.792871+00:00
-- url     : https://prove2.me/theorems/fa225625-9862-4f21-80f8-84e164b2e63a
-- title:
--   Sharp Intermediate Subgroup Bounds: product elementary Abelian even family
-- statement:
--   Index and interval count for the even-rank family
--   `H₀ × 1 ≤ H₀ × C_p^{2a}`.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L842-L852
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L842-L852

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

theorem SharpIntermediateSubgroupBounds.product_elementaryAbelian_even_family
    (H₀ : Type u) [Group H₀] [Fintype H₀]
    (p a : ℕ) [Fact p.Prime] :
    ((⊤ : Subgroup H₀).prod
      (⊥ : Subgroup (Multiplicative (Fin (2 * a) → ZMod p)))).index =
        p ^ (2 * a) ∧
      Fintype.card
          (Set.Ici ((⊤ : Subgroup H₀).prod
            (⊥ : Subgroup (Multiplicative (Fin (2 * a) → ZMod p))))) =
        totalQBinom p (2 * a) := by sorry
