-- Prove2me | Theorems.Thm_SoficGroups_KunThomFiberCoarea_diagonalImage_card
-- name    : SoficGroups.KunThomFiberCoarea.diagonalImage_card
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:23.501339+00:00
-- url     : https://prove2.me/theorems/8029a990-d42e-4d95-8a8e-a14f35a19804
-- title:
--   SoficGroups.KunThomFiberCoarea.diagonalImage_card
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea

theorem SoficGroups.KunThomFiberCoarea.diagonalImage_card {V : Type*} [DecidableEq V]
    (p : Equiv.Perm V) (U : Finset (V × V)) :
    (diagonalImage p U).card = U.card := by sorry
