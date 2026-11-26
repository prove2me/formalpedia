-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_normal_elementaryAbelian_quotient_interval_card_eq
-- name    : SharpIntermediateSubgroupBounds.normal_elementaryAbelian_quotient_interval_card_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:44:04.420538+00:00
-- url     : https://prove2.me/theorems/ad687b46-5063-5c99-9859-37c1c6dfccab
-- title:
--   Sharp Intermediate Subgroup Bounds: normal elementary Abelian quotient interval card eq
-- statement:
--   More generally, a normal inclusion whose quotient is elementary abelian attains equality.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L748-L764
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L748-L764

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

theorem SharpIntermediateSubgroupBounds.normal_elementaryAbelian_quotient_interval_card_eq {p a : ℕ}
    (H : Subgroup G) [H.Normal]
    (e : (G ⧸ H) ≃* Multiplicative (Fin a → ZMod p)) [Fact p.Prime] :
    Fintype.card (Set.Ici H) = totalQBinom p a := by sorry
