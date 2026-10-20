-- Prove2me | Theorems.Thm_SoficGroups_KunCompletedPrunedComponent_inducedBoundary_le_completed_boundary
-- name    : SoficGroups.KunCompletedPrunedComponent.inducedBoundary_le_completed_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.241177+00:00
-- url     : https://prove2.me/theorems/84bfb5a9-dbfd-4ea5-8d6b-fa08e98ce954
-- title:
--   SoficGroups.KunCompletedPrunedComponent.inducedBoundary_le_completed_boundary
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunCompletedPrunedComponent
open scoped BigOperators

theorem SoficGroups.KunCompletedPrunedComponent.inducedBoundary_le_completed_boundary
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (B Z : Finset V)
    (hZ : Z = Finset.univ \ B)
    (τ : ι → Equiv.Perm {x : V // x ∈ Z})
    (hτ : ∀ i (x : V) (hx : x ∈ Z) (_hy : σ i x ∈ Z),
      ((τ i ⟨x, hx⟩ : {x : V // x ∈ Z}) : V) = σ i x)
    (A : Finset {x : V // x ∈ Z}) :
    SoficGroups.inducedBoundary σ B
        (A.map (Function.Embedding.subtype (fun x : V => x ∈ Z))) ≤
      SoficGroups.boundary τ A := by sorry
