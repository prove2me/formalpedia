-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_Palomar_primePower_interval_bound_optimal
-- name    : SharpIntermediateSubgroupBounds.Palomar.primePower_interval_bound_optimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:03:47.133796+00:00
-- url     : https://prove2.me/theorems/4480430c-552b-5c1d-b519-9fcb83a0de60
-- title:
--   Palomar: prime Power interval bound optimal
-- statement:
--   Palomar-facing form of the exact prime-power theorem.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/Solution.lean#L22-L29
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/Solution.lean#L22-L29

import Definitions.Def_SharpIntermediateSubgroupBounds
import Definitions.Def_SharpIntermediateSubgroupBounds_Solution
import Theorems.Thm_SharpIntermediateSubgroupBounds_primePower_interval_bound_optimal

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open SharpIntermediateSubgroupBounds.Palomar
open scoped BigOperators Topology
open Filter Finset Real
noncomputable section

theorem SharpIntermediateSubgroupBounds.Palomar.primePower_interval_bound_optimal (p a : ℕ) [Fact p.Prime] :
    (∀ {G : Type*} [Group G] [Fintype G] (H : Subgroup G), H.index = p ^ a →
      Nat.card (Set.Ici H) ≤ totalQBinom p a) ∧
    Nat.card
        (Set.Ici (⊥ : Subgroup (Multiplicative (Fin a → ZMod p)))) =
      totalQBinom p a := by sorry
