-- Prove2me | Theorems.Thm_SoficGroups_KunThomFiberCoarea_permutationGraph_sdiff_bounds_of_matchedFiberEdges
-- name    : SoficGroups.KunThomFiberCoarea.permutationGraph_sdiff_bounds_of_matchedFiberEdges
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:24.345557+00:00
-- url     : https://prove2.me/theorems/cc0eec68-edcc-4f07-9961-a854b963c0de
-- title:
--   SoficGroups.KunThomFiberCoarea.permutationGraph_sdiff_bounds_of_matchedFiberEdges
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea

theorem SoficGroups.KunThomFiberCoarea.permutationGraph_sdiff_bounds_of_matchedFiberEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) (p : Equiv.Perm V)
    (hp : matchedFiberEdges U ⊆ SoficGroups.permutationGraph p) :
    (SoficGroups.permutationGraph p \ U).card ≤
        Fintype.card V - (matchedFiberEdges U).card ∧
      (U \ SoficGroups.permutationGraph p).card ≤
        (U \ matchedFiberEdges U).card := by sorry
