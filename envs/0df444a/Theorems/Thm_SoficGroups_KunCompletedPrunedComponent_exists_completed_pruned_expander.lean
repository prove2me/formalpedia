-- Prove2me | Theorems.Thm_SoficGroups_KunCompletedPrunedComponent_exists_completed_pruned_expander
-- name    : SoficGroups.KunCompletedPrunedComponent.exists_completed_pruned_expander
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.241177+00:00
-- url     : https://prove2.me/theorems/6c235b9a-cb21-4c80-b595-0ebe69e95efd
-- title:
--   SoficGroups.KunCompletedPrunedComponent.exists_completed_pruned_expander
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunCompletedPrunedComponent
open scoped BigOperators

theorem SoficGroups.KunCompletedPrunedComponent.exists_completed_pruned_expander
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (γ ell a : ℝ)
    (hgap : ell < γ)
    (hadd : ∀ A : Finset V,
      γ * min (A.card : ℝ)
          ((Fintype.card V : ℝ) - (A.card : ℝ)) -
        a * (Fintype.card V : ℝ) ≤
          (SoficGroups.boundary σ A : ℝ))
    (hsmall :
      2 * a * (2 * (γ - ell) + (Fintype.card ι : ℝ)) ≤
        (γ - ell) ^ 2) :
    ∃ (B : Finset V)
      (τ : ι → Equiv.Perm
        {x : V // x ∈ (Finset.univ \ B)}),
      2 * B.card ≤ Fintype.card V ∧
      (B.card : ℝ) ≤
        a * (Fintype.card V : ℝ) / (γ - ell) ∧
      (∀ i (x : V) (hx : x ∈ Finset.univ \ B)
        (_hy : σ i x ∈ Finset.univ \ B),
        ((τ i ⟨x, hx⟩ :
          {x : V // x ∈ Finset.univ \ B}) : V) = σ i x) ∧
      ∀ A : Finset {x : V // x ∈ Finset.univ \ B},
        ell * min (A.card : ℝ)
          ((Fintype.card {x : V // x ∈ Finset.univ \ B} : ℝ) -
            A.card) ≤ (SoficGroups.boundary τ A : ℝ) := by sorry
