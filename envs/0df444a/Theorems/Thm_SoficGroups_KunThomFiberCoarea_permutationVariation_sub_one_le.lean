-- Prove2me | Theorems.Thm_SoficGroups_KunThomFiberCoarea_permutationVariation_sub_one_le
-- name    : SoficGroups.KunThomFiberCoarea.permutationVariation_sub_one_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:23.501339+00:00
-- url     : https://prove2.me/theorems/bdefca82-abef-4195-b4c6-cdcfb6687f7f
-- title:
--   SoficGroups.KunThomFiberCoarea.permutationVariation_sub_one_le
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea

theorem SoficGroups.KunThomFiberCoarea.permutationVariation_sub_one_le
    {V ι : Type*} [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℕ) :
    permutationVariation σ (fun x => f x - 1) ≤
      permutationVariation σ f := by sorry
