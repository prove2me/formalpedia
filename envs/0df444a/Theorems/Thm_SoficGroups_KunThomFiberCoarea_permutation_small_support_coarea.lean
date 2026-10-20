-- Prove2me | Theorems.Thm_SoficGroups_KunThomFiberCoarea_permutation_small_support_coarea
-- name    : SoficGroups.KunThomFiberCoarea.permutation_small_support_coarea
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:23.501339+00:00
-- url     : https://prove2.me/theorems/316576a6-2e8c-42b0-8ad6-15d63b61ee4d
-- title:
--   SoficGroups.KunThomFiberCoarea.permutation_small_support_coarea
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea

theorem SoficGroups.KunThomFiberCoarea.permutation_small_support_coarea
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (h : ℝ)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (SoficGroups.boundary σ A : ℝ))
    (f : V → ℕ)
    (hhalf : 2 * (positiveNatSupport f).card ≤ Fintype.card V) :
    2 * h * (∑ x : V, f x) ≤
      (permutationVariation σ f : ℝ) := by sorry
