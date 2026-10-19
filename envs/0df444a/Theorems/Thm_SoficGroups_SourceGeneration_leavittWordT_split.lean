-- Prove2me | Theorems.Thm_SoficGroups_SourceGeneration_leavittWordT_split
-- name    : SoficGroups.SourceGeneration.leavittWordT_split
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.258421+00:00
-- url     : https://prove2.me/theorems/e0f4fe9f-6858-44e6-94b7-1936df63b1d7
-- title:
--   SoficGroups.SourceGeneration.leavittWordT_split
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.SourceGeneration
open scoped commutatorElement

theorem SoficGroups.SourceGeneration.leavittWordT_split (a : List (Fin 2)) :
    leavittWordT a =
      leavittS 0 * leavittWordT (a ++ [0]) +
        leavittS 1 * leavittWordT (a ++ [1]) := by sorry
