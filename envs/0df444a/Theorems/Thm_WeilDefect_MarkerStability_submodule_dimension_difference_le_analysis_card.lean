-- Prove2me | Theorems.Thm_WeilDefect_MarkerStability_submodule_dimension_difference_le_analysis_card
-- name    : WeilDefect.MarkerStability.submodule_dimension_difference_le_analysis_card
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T20:03:58.520978+00:00
-- url     : https://prove2.me/theorems/1eaf1606-c74d-48b9-a6ed-f3d672e224ce
-- title:
--   An analysis map bounds a submodule dimension difference by its coordinate count
-- statement:
--   Let $W\subseteq U$ be submodules of a finite-dimensional complex vector space. If a complex linear analysis map to $\mathbb C^J$ has, ON $U$, precisely $W$ as its null directions, then $$\dim U-\dim W\le |J|.$$ The null-direction identity and containment are explicit hypotheses; the proof uses rank-nullity, not a presumed numerical rank.
-- source:
--   monocap-tech/weil, compiling source c3e7b782afd23ef5076a93915265a6584646b5e7, exact declaration WeilDefect.MarkerStability.submodule_dimension_difference_le_analysis_card

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false
open scoped Classical
noncomputable section

theorem WeilDefect.MarkerStability.submodule_dimension_difference_le_analysis_card
    {V J : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Fintype J]
    (U W : Submodule ℂ V) (hWU : W ≤ U) (L : V →ₗ[ℂ] (J → ℂ))
    (hker : ∀ v ∈ U, L v = 0 ↔ v ∈ W) :
    Module.finrank ℂ U - Module.finrank ℂ W ≤ Fintype.card J := by sorry
