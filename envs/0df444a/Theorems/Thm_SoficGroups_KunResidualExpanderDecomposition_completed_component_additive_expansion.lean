-- Prove2me | Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_completed_component_additive_expansion
-- name    : SoficGroups.KunResidualExpanderDecomposition.completed_component_additive_expansion
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.241177+00:00
-- url     : https://prove2.me/theorems/d92d1cbb-6e54-4dff-bd47-5f3562167c94
-- title:
--   SoficGroups.KunResidualExpanderDecomposition.completed_component_additive_expansion
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunResidualExpanderDecomposition
open Filter Topology
open scoped BigOperators symmDiff

theorem SoficGroups.KunResidualExpanderDecomposition.completed_component_additive_expansion
    {V ι : Type*} [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (C : Finset V)
    (τ : ι → Equiv.Perm {x : V // x ∈ C})
    (hτ : ∀ i (x : V) (hx : x ∈ C) (_hy : σ i x ∈ C),
      ((τ i ⟨x, hx⟩ : {x : V // x ∈ C}) : V) = σ i x)
    (γ : ℝ)
    (hexpand : ∀ E : Finset V, E ⊆ C →
      2 * E.card ≤ C.card →
        γ * (E.card : ℝ) ≤ (SoficGroups.boundary σ E : ℝ)) :
    ∀ A : Finset {x : V // x ∈ C},
      γ * min (A.card : ℝ) ((C.card : ℝ) - A.card) -
          (SoficGroups.boundary σ C : ℝ) ≤
        (SoficGroups.boundary τ A : ℝ) := by sorry
