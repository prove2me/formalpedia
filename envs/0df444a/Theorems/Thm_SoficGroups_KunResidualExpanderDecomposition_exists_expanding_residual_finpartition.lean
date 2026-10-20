-- Prove2me | Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_exists_expanding_residual_finpartition
-- name    : SoficGroups.KunResidualExpanderDecomposition.exists_expanding_residual_finpartition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.241177+00:00
-- url     : https://prove2.me/theorems/1a0a6974-6573-4d55-ba77-ece6990226c2
-- title:
--   SoficGroups.KunResidualExpanderDecomposition.exists_expanding_residual_finpartition
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

theorem SoficGroups.KunResidualExpanderDecomposition.exists_expanding_residual_finpartition
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (B : Finset V) (γ α : ℝ)
    (hα : 0 ≤ α)
    (himprove : ∀ T : Finset V, T ⊆ Finset.univ \ B →
      (SoficGroups.boundary σ T : ℝ) < γ * (T.card : ℝ) →
      ∃ U : Finset V, 3 * (U ∆ T).card < T.card ∧
        (SoficGroups.boundary σ U : ℝ) ≤ α * (U.card : ℝ))
    (R : Finset V) (hRB : R ⊆ Finset.univ \ B) :
    ∃ P : Finpartition R,
      (∀ C ∈ P.parts, ∀ E : Finset V, E ⊆ C →
        2 * E.card ≤ C.card →
          γ * (E.card : ℝ) ≤ (SoficGroups.boundary σ E : ℝ)) ∧
      (∑ C ∈ P.parts, (SoficGroups.boundary σ C : ℝ)) ≤
        (SoficGroups.boundary σ R : ℝ) +
          4 * α * (R.card : ℝ) := by sorry
