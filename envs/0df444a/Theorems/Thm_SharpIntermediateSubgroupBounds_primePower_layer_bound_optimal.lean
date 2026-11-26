-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_primePower_layer_bound_optimal
-- name    : SharpIntermediateSubgroupBounds.primePower_layer_bound_optimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:00:32.633716+00:00
-- url     : https://prove2.me/theorems/25e77265-12aa-50ab-86e2-e83b42b5b00e
-- title:
--   Sharp Intermediate Subgroup Bounds: prime Power layer bound optimal
-- statement:
--   The fixed-layer Gaussian estimate packaged with its elementary-abelian
--   equality witness.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L856-L867
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L856-L867

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

theorem SharpIntermediateSubgroupBounds.primePower_layer_bound_optimal (p a k : ℕ) [Fact p.Prime]
    (hk : k ≤ a) :
    (∀ {G : Type*} [Group G] [Fintype G] (H : Subgroup G),
      H.index = p ^ a →
        (primePowerLayer p k H ⊤).card ≤ qBinom p a k) ∧
      (primePowerLayer p k
        (⊥ : Subgroup (Multiplicative (Fin a → ZMod p))) ⊤).card =
        qBinom p a k := by sorry
