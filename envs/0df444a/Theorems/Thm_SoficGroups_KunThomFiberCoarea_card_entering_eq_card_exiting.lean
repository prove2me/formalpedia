-- Prove2me | Theorems.Thm_SoficGroups_KunThomFiberCoarea_card_entering_eq_card_exiting
-- name    : SoficGroups.KunThomFiberCoarea.card_entering_eq_card_exiting
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:23.501339+00:00
-- url     : https://prove2.me/theorems/2867eebd-ba20-444d-b941-3ecab5d65bfc
-- title:
--   SoficGroups.KunThomFiberCoarea.card_entering_eq_card_exiting
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea

theorem SoficGroups.KunThomFiberCoarea.card_entering_eq_card_exiting
    {V : Type*} [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (A : Finset V) :
    (Finset.univ.filter fun x => x ∉ A ∧ p x ∈ A).card =
      (A.filter fun x => p x ∉ A).card := by sorry
