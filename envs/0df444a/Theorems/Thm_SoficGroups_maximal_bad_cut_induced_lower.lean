-- Prove2me | Theorems.Thm_SoficGroups_maximal_bad_cut_induced_lower
-- name    : SoficGroups.maximal_bad_cut_induced_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:18.478977+00:00
-- url     : https://prove2.me/theorems/8527cc7f-6370-4006-9204-714657b86eb6
-- title:
--   SoficGroups.maximal_bad_cut_induced_lower
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

theorem SoficGroups.maximal_bad_cut_induced_lower {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (B E : Finset V) (ell : ℝ)
    (hB : (boundary σ B : ℝ) ≤ ell * (B.card : ℝ))
    (hmax : ∀ A : Finset V,
      2 * A.card ≤ Fintype.card V →
      (boundary σ A : ℝ) < ell * (A.card : ℝ) → A.card ≤ B.card)
    (hdisj : Disjoint B E) (hne : E.Nonempty)
    (hhalf : 2 * (B ∪ E).card ≤ Fintype.card V) :
    ell * (E.card : ℝ) ≤ (inducedBoundary σ B E : ℝ) := by sorry
