-- Prove2me | Theorems.Thm_SoficGroups_prune_permutation_multigraph
-- name    : SoficGroups.prune_permutation_multigraph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:18.478977+00:00
-- url     : https://prove2.me/theorems/67e78e55-5e10-4c9a-b6d2-2f16d14774ea
-- title:
--   SoficGroups.prune_permutation_multigraph
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

theorem SoficGroups.prune_permutation_multigraph {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (γ ell a : ℝ) (B : Finset V)
    (hgap : ell < γ)
    (hadd : ∀ A : Finset V,
      γ * min (A.card : ℝ) ((Fintype.card V : ℝ) - (A.card : ℝ)) -
          a * (Fintype.card V : ℝ) ≤ (boundary σ A : ℝ))
    (hBhalf : 2 * B.card ≤ Fintype.card V)
    (hB : (boundary σ B : ℝ) ≤ ell * (B.card : ℝ))
    (hmax : ∀ A : Finset V,
      2 * A.card ≤ Fintype.card V →
      (boundary σ A : ℝ) < ell * (A.card : ℝ) → A.card ≤ B.card)
    (hsmall :
      2 * a * (2 * (γ - ell) + (Fintype.card ι : ℝ)) ≤ (γ - ell) ^ 2)
    (E : Finset V) (hdisj : Disjoint B E)
    (hEhalf : 2 * E.card ≤ Fintype.card V - B.card) :
    ell * (E.card : ℝ) ≤ (inducedBoundary σ B E : ℝ) := by sorry
