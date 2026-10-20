-- Prove2me | Theorems.Thm_SoficGroups_KunThomFiberCoarea_unmatched_vertices_le_zero_and_excess
-- name    : SoficGroups.KunThomFiberCoarea.unmatched_vertices_le_zero_and_excess
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:24.345557+00:00
-- url     : https://prove2.me/theorems/7254c204-a5be-42dd-9847-b4348bb35dc3
-- title:
--   SoficGroups.KunThomFiberCoarea.unmatched_vertices_le_zero_and_excess
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea

theorem SoficGroups.KunThomFiberCoarea.unmatched_vertices_le_zero_and_excess
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) :
    Fintype.card V - (matchedFiberEdges U).card ≤
      (Finset.univ.filter fun x : V => firstMultiplicity U x = 0).card +
        (∑ x : V, (firstMultiplicity U x - 1 : ℕ)) +
        2 * (∑ x : V, (secondMultiplicity U x - 1 : ℕ)) := by sorry
