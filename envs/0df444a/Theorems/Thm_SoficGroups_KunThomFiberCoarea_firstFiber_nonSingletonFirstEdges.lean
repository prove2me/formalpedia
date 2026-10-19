-- Prove2me | Theorems.Thm_SoficGroups_KunThomFiberCoarea_firstFiber_nonSingletonFirstEdges
-- name    : SoficGroups.KunThomFiberCoarea.firstFiber_nonSingletonFirstEdges
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:24.345557+00:00
-- url     : https://prove2.me/theorems/92ec9803-ce70-4dc1-a1e3-559faccecf49
-- title:
--   SoficGroups.KunThomFiberCoarea.firstFiber_nonSingletonFirstEdges
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea

theorem SoficGroups.KunThomFiberCoarea.firstFiber_nonSingletonFirstEdges
    {V : Type*} [DecidableEq V]
    (U : Finset (V × V)) (x : V) :
    firstFiber (nonSingletonFirstEdges U) x =
      if firstMultiplicity U x ≠ 1 then firstFiber U x else ∅ := by sorry
