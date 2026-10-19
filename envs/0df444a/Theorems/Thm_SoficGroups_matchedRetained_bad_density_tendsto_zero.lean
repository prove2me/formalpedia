-- Prove2me | Theorems.Thm_SoficGroups_matchedRetained_bad_density_tendsto_zero
-- name    : SoficGroups.matchedRetained_bad_density_tendsto_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.023082+00:00
-- url     : https://prove2.me/theorems/76e7be38-487a-4b86-819b-49757c2d479b
-- title:
--   SoficGroups.matchedRetained_bad_density_tendsto_zero
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

theorem SoficGroups.matchedRetained_bad_density_tendsto_zero
    {V : ℕ → Type*} [∀ n, DecidableEq (V n)]
    (U : ∀ n, Finset (V n)) (hU : ∀ n, (U n).Nonempty)
    (P : ∀ n, Finpartition (U n))
    (R : ∀ n, Finset (Finset (V n)))
    (hR : ∀ n, R n ⊆ (P n).parts)
    (hRne : ∀ n, (R n).Nonempty)
    (hdiscard : Tendsto
      (fun n => (((U n \ matchedRetainedSupport (R n)).card : ℝ) /
        (U n).card)) atTop (𝓝 0))
    (B : ∀ n, Finset (V n))
    (hbad : Tendsto
      (fun n => (((U n ∩ B n).card : ℝ) / (U n).card))
      atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        (((matchedRetainedSupport (R n) ∩ B n).card : ℝ) /
          (matchedRetainedSupport (R n)).card))
      atTop (𝓝 0) := by sorry
