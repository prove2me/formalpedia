-- Prove2me | Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_original_boundary_le_completed_add_component_boundary
-- name    : SoficGroups.KunResidualExpanderDecomposition.original_boundary_le_completed_add_component_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.241177+00:00
-- url     : https://prove2.me/theorems/4e1c6fab-d5ce-45f2-99f9-72b1a294160e
-- title:
--   SoficGroups.KunResidualExpanderDecomposition.original_boundary_le_completed_add_component_boundary
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

theorem SoficGroups.KunResidualExpanderDecomposition.original_boundary_le_completed_add_component_boundary
    {V ι : Type*} [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (C : Finset V)
    (τ : ι → Equiv.Perm {x : V // x ∈ C})
    (hτ : ∀ i (x : V) (hx : x ∈ C) (_hy : σ i x ∈ C),
      ((τ i ⟨x, hx⟩ : {x : V // x ∈ C}) : V) = σ i x)
    (A : Finset {x : V // x ∈ C}) :
    SoficGroups.boundary σ
        (A.map (Function.Embedding.subtype (fun x : V => x ∈ C))) ≤
      SoficGroups.boundary τ A +
        SoficGroups.boundary σ C := by sorry
