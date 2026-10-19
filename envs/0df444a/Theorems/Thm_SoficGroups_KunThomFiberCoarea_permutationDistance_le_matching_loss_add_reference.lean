-- Prove2me | Theorems.Thm_SoficGroups_KunThomFiberCoarea_permutationDistance_le_matching_loss_add_reference
-- name    : SoficGroups.KunThomFiberCoarea.permutationDistance_le_matching_loss_add_reference
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:24.345557+00:00
-- url     : https://prove2.me/theorems/c673b17d-dbcc-4142-98e5-29537ef6ce74
-- title:
--   SoficGroups.KunThomFiberCoarea.permutationDistance_le_matching_loss_add_reference
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea

theorem SoficGroups.KunThomFiberCoarea.permutationDistance_le_matching_loss_add_reference
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) (q p : Equiv.Perm V)
    (hq : matchedFiberEdges U ⊆ SoficGroups.permutationGraph q) :
    SoficGroups.permutationDistance q p ≤
      Fintype.card V - (matchedFiberEdges U).card +
        (U \ SoficGroups.permutationGraph p).card := by sorry
