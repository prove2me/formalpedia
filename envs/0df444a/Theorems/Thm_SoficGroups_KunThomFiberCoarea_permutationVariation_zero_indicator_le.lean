-- Prove2me | Theorems.Thm_SoficGroups_KunThomFiberCoarea_permutationVariation_zero_indicator_le
-- name    : SoficGroups.KunThomFiberCoarea.permutationVariation_zero_indicator_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:23.501339+00:00
-- url     : https://prove2.me/theorems/e0461f76-13d7-47f1-91b4-4471545c648b
-- title:
--   SoficGroups.KunThomFiberCoarea.permutationVariation_zero_indicator_le
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea

theorem SoficGroups.KunThomFiberCoarea.permutationVariation_zero_indicator_le
    {V ι : Type*} [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℕ) :
    permutationVariation σ (fun x => if f x = 0 then 1 else 0) ≤
      permutationVariation σ f := by sorry
