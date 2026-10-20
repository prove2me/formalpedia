-- Prove2me | Theorems.Thm_SoficGroups_matchedCore_missing_density_tendsto_zero
-- name    : SoficGroups.matchedCore_missing_density_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.258421+00:00
-- url     : https://prove2.me/theorems/0ca05fa5-c4c6-4286-bf5d-17bca9e32ecd
-- title:
--   SoficGroups.matchedCore_missing_density_tendsto_zero
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

theorem SoficGroups.matchedCore_missing_density_tendsto_zero
    {V : ℕ → Type*} [∀ n, DecidableEq (V n)]
    (U : ∀ n, Finset (V n)) (P : ∀ n, Finpartition (U n))
    (R : ∀ n, Finset (Finset (V n)))
    (hR : ∀ n, R n ⊆ (P n).parts)
    (D : ∀ n, Finset (V n) → Finset (V n))
    (hdiscard : Tendsto
      (fun n => (((U n \ matchedRetainedSupport (R n)).card : ℝ) /
        (U n).card)) atTop (𝓝 0))
    (hsymm : Tendsto
      (fun n =>
        ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) / (U n).card)
      atTop (𝓝 0)) :
    Tendsto
      (fun n => (((U n \ matchedCore (R n) (D n)).card : ℝ) /
        (U n).card)) atTop (𝓝 0) := by sorry
