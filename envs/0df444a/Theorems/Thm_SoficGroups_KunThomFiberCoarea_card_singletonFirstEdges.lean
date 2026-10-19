-- Prove2me | Theorems.Thm_SoficGroups_KunThomFiberCoarea_card_singletonFirstEdges
-- name    : SoficGroups.KunThomFiberCoarea.card_singletonFirstEdges
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:24.345557+00:00
-- url     : https://prove2.me/theorems/9d28577b-2e17-482c-b870-8fa1b660ee59
-- title:
--   SoficGroups.KunThomFiberCoarea.card_singletonFirstEdges
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea

theorem SoficGroups.KunThomFiberCoarea.card_singletonFirstEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) :
    (singletonFirstEdges U).card =
      (singletonSupport (firstMultiplicity U)).card := by sorry
