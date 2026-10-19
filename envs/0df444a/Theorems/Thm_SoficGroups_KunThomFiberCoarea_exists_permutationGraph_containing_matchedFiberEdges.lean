-- Prove2me | Theorems.Thm_SoficGroups_KunThomFiberCoarea_exists_permutationGraph_containing_matchedFiberEdges
-- name    : SoficGroups.KunThomFiberCoarea.exists_permutationGraph_containing_matchedFiberEdges
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:24.345557+00:00
-- url     : https://prove2.me/theorems/9ffb22a7-4fb6-4fdf-bc92-b23028a9b101
-- title:
--   SoficGroups.KunThomFiberCoarea.exists_permutationGraph_containing_matchedFiberEdges
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea

theorem SoficGroups.KunThomFiberCoarea.exists_permutationGraph_containing_matchedFiberEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) :
    ∃ p : Equiv.Perm V,
      matchedFiberEdges U ⊆ SoficGroups.permutationGraph p := by sorry
