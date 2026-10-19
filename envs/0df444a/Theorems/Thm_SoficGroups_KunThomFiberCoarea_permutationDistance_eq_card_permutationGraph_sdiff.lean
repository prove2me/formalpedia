-- Prove2me | Theorems.Thm_SoficGroups_KunThomFiberCoarea_permutationDistance_eq_card_permutationGraph_sdiff
-- name    : SoficGroups.KunThomFiberCoarea.permutationDistance_eq_card_permutationGraph_sdiff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:24.345557+00:00
-- url     : https://prove2.me/theorems/5ab6ff7b-8e33-4d2e-b16d-eb01e0e9b637
-- title:
--   SoficGroups.KunThomFiberCoarea.permutationDistance_eq_card_permutationGraph_sdiff
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea

theorem SoficGroups.KunThomFiberCoarea.permutationDistance_eq_card_permutationGraph_sdiff
    {V : Type*} [Fintype V] [DecidableEq V]
    (p q : Equiv.Perm V) :
    SoficGroups.permutationDistance p q =
      (SoficGroups.permutationGraph p \
        SoficGroups.permutationGraph q).card := by sorry
