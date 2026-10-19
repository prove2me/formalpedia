-- Prove2me | Theorems.Thm_SoficGroups_KunResidualRetainedSelection_matchedRetained_boundary_density_tendsto_zero
-- name    : SoficGroups.KunResidualRetainedSelection.matchedRetained_boundary_density_tendsto_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/bc13564c-70f5-4977-b49c-19378e624848
-- title:
--   SoficGroups.KunResidualRetainedSelection.matchedRetained_boundary_density_tendsto_zero
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

theorem SoficGroups.KunResidualRetainedSelection.matchedRetained_boundary_density_tendsto_zero
    {V : ℕ → Type*} [∀ n, DecidableEq (V n)]
    {ι : Type*} [Fintype ι]
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (U : ∀ n, Finset (V n)) (hU : ∀ n, (U n).Nonempty)
    (P : ∀ n, Finpartition (U n))
    (R : ∀ n, Finset (Finset (V n)))
    (hR : ∀ n, R n ⊆ (P n).parts)
    (hRne : ∀ n, (R n).Nonempty)
    (hdiscard : Tendsto
      (fun n => (((U n \ SoficGroups.matchedRetainedSupport (R n)).card : ℝ) /
        (U n).card)) atTop (𝓝 0))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts, (SoficGroups.boundary (σ n) C : ℝ)) /
          (U n).card) atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        (∑ C ∈ R n, (SoficGroups.boundary (σ n) C : ℝ)) /
          (SoficGroups.matchedRetainedSupport (R n)).card)
      atTop (𝓝 0) := by sorry
