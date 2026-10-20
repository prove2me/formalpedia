-- Prove2me | Theorems.Thm_SoficGroups_KunResidualRetainedSelection_exists_matchedRetained_part_boundary_and_bad_density_le
-- name    : SoficGroups.KunResidualRetainedSelection.exists_matchedRetained_part_boundary_and_bad_density_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/e81833b8-7178-4a18-841a-279251f33b0e
-- title:
--   SoficGroups.KunResidualRetainedSelection.exists_matchedRetained_part_boundary_and_bad_density_le
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunResidualRetainedSelection
open Filter Topology
open scoped BigOperators Pointwise symmDiff

theorem SoficGroups.KunResidualRetainedSelection.exists_matchedRetained_part_boundary_and_bad_density_le
    {V ι : Type*} [DecidableEq V] [Fintype ι]
    (σ : ι → Equiv.Perm V) {U : Finset V}
    (P : Finpartition U) (R : Finset (Finset V))
    (hR : R ⊆ P.parts) (hRne : R.Nonempty) (B : Finset V) :
    ∃ C ∈ R,
      (SoficGroups.boundary σ C : ℝ) / C.card ≤
        ((∑ D ∈ R, (SoficGroups.boundary σ D : ℝ)) +
          ((SoficGroups.matchedRetainedSupport R ∩ B).card : ℝ)) /
            (SoficGroups.matchedRetainedSupport R).card ∧
      ((C ∩ B).card : ℝ) / C.card ≤
        ((∑ D ∈ R, (SoficGroups.boundary σ D : ℝ)) +
          ((SoficGroups.matchedRetainedSupport R ∩ B).card : ℝ)) /
            (SoficGroups.matchedRetainedSupport R).card := by sorry
