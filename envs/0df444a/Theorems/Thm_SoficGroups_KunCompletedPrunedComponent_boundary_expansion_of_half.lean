-- Prove2me | Theorems.Thm_SoficGroups_KunCompletedPrunedComponent_boundary_expansion_of_half
-- name    : SoficGroups.KunCompletedPrunedComponent.boundary_expansion_of_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.241177+00:00
-- url     : https://prove2.me/theorems/8aa2db73-23f9-4bb9-8ee1-ffac16c5691a
-- title:
--   SoficGroups.KunCompletedPrunedComponent.boundary_expansion_of_half
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunCompletedPrunedComponent
open scoped BigOperators

theorem SoficGroups.KunCompletedPrunedComponent.boundary_expansion_of_half
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (h : ℝ)
    (hhalf : ∀ A : Finset V,
      2 * A.card ≤ Fintype.card V →
        h * (A.card : ℝ) ≤ (SoficGroups.boundary σ A : ℝ)) :
    ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (SoficGroups.boundary σ A : ℝ) := by sorry
