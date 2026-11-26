-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_primePower_interval_bound_optimal
-- name    : SharpIntermediateSubgroupBounds.primePower_interval_bound_optimal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:44:16.032802+00:00
-- url     : https://prove2.me/theorems/c6751a7b-5ed2-4400-b5f5-fe1aba3b2702
-- title:
--   Sharp Intermediate Subgroup Bounds: prime Power interval bound optimal
-- statement:
--   The exact prime-power theorem packaged as an optimality statement: the bound holds for
--   every finite inclusion of index `p ^ a`, and the elementary abelian inclusion attains it.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L871-L879
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L871-L879

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

theorem SharpIntermediateSubgroupBounds.primePower_interval_bound_optimal (p a : ℕ) [Fact p.Prime] :
    (∀ {G : Type*} [Group G] [Fintype G] (H : Subgroup G), H.index = p ^ a →
      Fintype.card (Set.Ici H) ≤ totalQBinom p a) ∧
    Fintype.card
        (Set.Ici (⊥ : Subgroup (Multiplicative (Fin a → ZMod p)))) = totalQBinom p a := by sorry
