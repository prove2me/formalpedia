-- Prove2me | Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_exists_minimum_sparse_residual_cut
-- name    : SoficGroups.KunResidualExpanderDecomposition.exists_minimum_sparse_residual_cut
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.241177+00:00
-- url     : https://prove2.me/theorems/c0ccfebc-dc36-48af-ab3c-89eeaec7e953
-- title:
--   SoficGroups.KunResidualExpanderDecomposition.exists_minimum_sparse_residual_cut
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

theorem SoficGroups.KunResidualExpanderDecomposition.exists_minimum_sparse_residual_cut {V ι : Type*}
    [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (R : Finset V) (γ : ℝ)
    (hsparse : ∃ T : Finset V, T ⊆ R ∧
      (SoficGroups.boundary σ T : ℝ) < γ * (T.card : ℝ)) :
    ∃ T : Finset V, T ⊆ R ∧
      (SoficGroups.boundary σ T : ℝ) < γ * (T.card : ℝ) ∧
      ∀ E : Finset V, E ⊆ R →
        (SoficGroups.boundary σ E : ℝ) < γ * (E.card : ℝ) →
        T.card ≤ E.card := by sorry
