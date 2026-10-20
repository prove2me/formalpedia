-- Prove2me | Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_minimum_sparse_cut_expands_close_residual_part
-- name    : SoficGroups.KunResidualExpanderDecomposition.minimum_sparse_cut_expands_close_residual_part
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.241177+00:00
-- url     : https://prove2.me/theorems/e3bbfab5-8b1e-4fee-aa28-384ca0057c29
-- title:
--   SoficGroups.KunResidualExpanderDecomposition.minimum_sparse_cut_expands_close_residual_part
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

theorem SoficGroups.KunResidualExpanderDecomposition.minimum_sparse_cut_expands_close_residual_part
    {V ι : Type*} [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (R T U : Finset V) (γ : ℝ)
    (hTR : T ⊆ R)
    (hminimum : ∀ E : Finset V, E ⊆ R →
      (SoficGroups.boundary σ E : ℝ) < γ * (E.card : ℝ) →
      T.card ≤ E.card)
    (hclose : 3 * (U ∆ T).card < T.card) :
    ∀ E : Finset V, E ⊆ R ∩ U →
      2 * E.card ≤ (R ∩ U).card →
      γ * (E.card : ℝ) ≤ (SoficGroups.boundary σ E : ℝ) := by sorry
