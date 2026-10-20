-- Prove2me | Theorems.Thm_SoficGroups_KunActualFirstStageReferenceExpansion_completed_actual_component_additive_expansion_of_reference
-- name    : SoficGroups.KunActualFirstStageReferenceExpansion.completed_actual_component_additive_expansion_of_reference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:32.70599+00:00
-- url     : https://prove2.me/theorems/8d9eeb95-5b84-41b7-b863-e0ce3d1d01a1
-- title:
--   SoficGroups.KunActualFirstStageReferenceExpansion.completed_actual_component_additive_expansion_of_reference
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFirstStageReferenceExpansion
open Filter Topology
open scoped BigOperators

theorem SoficGroups.KunActualFirstStageReferenceExpansion.completed_actual_component_additive_expansion_of_reference
    {V ι : Type*} [Fintype ι] [DecidableEq V]
    (σref σact : ι → Equiv.Perm V) (C : Finset V)
    (τ : ι → Equiv.Perm {x : V // x ∈ C})
    (hτ : ∀ i (x : V) (hx : x ∈ C) (_hy : σact i x ∈ C),
      ((τ i ⟨x, hx⟩ : {x : V // x ∈ C}) : V) = σact i x)
    (γ : ℝ)
    (hexpand : ∀ E : Finset V, E ⊆ C →
      2 * E.card ≤ C.card →
        γ * (E.card : ℝ) ≤ (SoficGroups.boundary σref E : ℝ)) :
    ∀ E : Finset {x : V // x ∈ C},
      γ * min (E.card : ℝ) ((C.card : ℝ) - E.card) -
        ((SoficGroups.boundary σref C : ℝ) +
          2 * (componentGeneratorDisagreement C σref σact : ℝ)) ≤
        (SoficGroups.boundary τ E : ℝ) := by sorry
