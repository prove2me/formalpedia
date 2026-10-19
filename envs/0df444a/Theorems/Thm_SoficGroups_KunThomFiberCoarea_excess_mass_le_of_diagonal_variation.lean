-- Prove2me | Theorems.Thm_SoficGroups_KunThomFiberCoarea_excess_mass_le_of_diagonal_variation
-- name    : SoficGroups.KunThomFiberCoarea.excess_mass_le_of_diagonal_variation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:23.501339+00:00
-- url     : https://prove2.me/theorems/1e9345fb-e791-46c0-ab8b-582e85effa20
-- title:
--   SoficGroups.KunThomFiberCoarea.excess_mass_le_of_diagonal_variation
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea

theorem SoficGroups.KunThomFiberCoarea.excess_mass_le_of_diagonal_variation
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (h : ℝ)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (SoficGroups.boundary σ A : ℝ))
    (f : V → ℕ) (B : ℕ)
    (hsingle : Fintype.card V ≤ 2 * (singletonSupport f).card)
    (hvariation : permutationVariation σ f ≤ 2 * B) :
    h * (∑ x : V, (f x - 1 : ℕ)) ≤ (B : ℝ) := by sorry
