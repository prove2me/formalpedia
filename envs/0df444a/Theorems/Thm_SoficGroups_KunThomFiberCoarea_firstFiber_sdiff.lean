-- Prove2me | Theorems.Thm_SoficGroups_KunThomFiberCoarea_firstFiber_sdiff
-- name    : SoficGroups.KunThomFiberCoarea.firstFiber_sdiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:23.501339+00:00
-- url     : https://prove2.me/theorems/693c8903-e367-4e57-9300-fff4f348568a
-- title:
--   SoficGroups.KunThomFiberCoarea.firstFiber_sdiff
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea

theorem SoficGroups.KunThomFiberCoarea.firstFiber_sdiff {V : Type*} [DecidableEq V]
    (U W : Finset (V × V)) (x : V) :
    firstFiber (U \ W) x = firstFiber U x \ firstFiber W x := by sorry
