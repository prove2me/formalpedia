-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_product_elementaryAbelian_even_interval_card_eq
-- name    : SharpIntermediateSubgroupBounds.product_elementaryAbelian_even_interval_card_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:00:21.370008+00:00
-- url     : https://prove2.me/theorems/355435d1-db1e-51ef-b889-72a1fce5954b
-- title:
--   Sharp Intermediate Subgroup Bounds: product elementary Abelian even interval card eq
-- statement:
--   The even-rank product family appearing in the asymptotic sharpness
--   statement of the manuscript.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L831-L838
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L831-L838

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

theorem SharpIntermediateSubgroupBounds.product_elementaryAbelian_even_interval_card_eq
    (H₀ : Type u) [Group H₀] [Fintype H₀]
    (p a : ℕ) [Fact p.Prime] :
    Fintype.card
        (Set.Ici ((⊤ : Subgroup H₀).prod
          (⊥ : Subgroup (Multiplicative (Fin (2 * a) → ZMod p))))) =
      totalQBinom p (2 * a) := by sorry
