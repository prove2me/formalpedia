-- Prove2me | Theorems.Thm_SoficGroups_KunCompletedComponentMidrankVariation_permutationRealVariation_sq_le_card_mul_energy
-- name    : SoficGroups.KunCompletedComponentMidrankVariation.permutationRealVariation_sq_le_card_mul_energy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/01b2c149-7a56-466b-8310-ec29ff80e332
-- title:
--   SoficGroups.KunCompletedComponentMidrankVariation.permutationRealVariation_sq_le_card_mul_energy
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunCompletedComponentMidrankVariation
open Filter Topology
open scoped BigOperators

theorem SoficGroups.KunCompletedComponentMidrankVariation.permutationRealVariation_sq_le_card_mul_energy
    {V ι : Type*} [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) :
    permutationRealVariation σ f ^ 2 ≤
      ((Fintype.card ι : ℝ) * Fintype.card V) *
        (∑ i : ι, ∑ x : V, (f (σ i x) - f x) ^ 2) := by sorry
