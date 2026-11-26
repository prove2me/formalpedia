-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_elementaryAbelian_primePowerLayer_card_eq_qBinom
-- name    : SharpIntermediateSubgroupBounds.elementaryAbelian_primePowerLayer_card_eq_qBinom
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:43:48.297946+00:00
-- url     : https://prove2.me/theorems/94bf201f-4a5e-59db-b329-3651d166e8d2
-- title:
--   Sharp Intermediate Subgroup Bounds: elementary Abelian prime Power Layer card eq q Binom
-- statement:
--   Every prime-power layer of an elementary abelian group attains the
--   Gaussian layer bound.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L681-L720
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L681-L720

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

theorem SharpIntermediateSubgroupBounds.elementaryAbelian_primePowerLayer_card_eq_qBinom (p a k : ℕ)
    [Fact p.Prime] (hk : k ≤ a) :
    (primePowerLayer p k
      (⊥ : Subgroup (Multiplicative (Fin a → ZMod p))) ⊤).card =
        qBinom p a k := by sorry
