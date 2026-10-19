-- Prove2me | Theorems.Thm_SoficGroups_finite_union_bad_density_tendsto_zero
-- name    : SoficGroups.finite_union_bad_density_tendsto_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.258421+00:00
-- url     : https://prove2.me/theorems/dfe2fb36-9699-4b6b-aa87-9d43bfba66b3
-- title:
--   SoficGroups.finite_union_bad_density_tendsto_zero
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

theorem SoficGroups.finite_union_bad_density_tendsto_zero
    {α : ℕ → Type*} [∀ n, DecidableEq (α n)]
    {ι : Type*} (I : Finset ι)
    (V : ∀ n, Finset (α n)) (B : ∀ n, ι → Finset (α n))
    (hbad : ∀ i ∈ I, Tendsto
      (fun n => (((V n ∩ B n i).card : ℝ) / (V n).card))
      atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        (((V n ∩ I.biUnion (B n)).card : ℝ) / (V n).card))
      atTop (𝓝 0) := by sorry
