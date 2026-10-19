-- Prove2me | Theorems.Thm_SoficGroups_exists_maximal_bad_cut
-- name    : SoficGroups.exists_maximal_bad_cut
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:18.478977+00:00
-- url     : https://prove2.me/theorems/2773a14c-e8e6-4aee-9307-93bc2c717a1f
-- title:
--   SoficGroups.exists_maximal_bad_cut
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff

theorem SoficGroups.exists_maximal_bad_cut {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (ell : ℝ) :
    ∃ B : Finset V,
      2 * B.card ≤ Fintype.card V ∧
      (boundary σ B : ℝ) ≤ ell * (B.card : ℝ) ∧
      ∀ A : Finset V,
        2 * A.card ≤ Fintype.card V →
        (boundary σ A : ℝ) < ell * (A.card : ℝ) → A.card ≤ B.card := by sorry
