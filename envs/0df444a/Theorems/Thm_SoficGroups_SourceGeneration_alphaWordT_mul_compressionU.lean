-- Prove2me | Theorems.Thm_SoficGroups_SourceGeneration_alphaWordT_mul_compressionU
-- name    : SoficGroups.SourceGeneration.alphaWordT_mul_compressionU
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.258421+00:00
-- url     : https://prove2.me/theorems/b0f145c3-569e-4145-bab8-c3d95833b1e5
-- title:
--   SoficGroups.SourceGeneration.alphaWordT_mul_compressionU
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

theorem SoficGroups.SourceGeneration.alphaWordT_mul_compressionU (i : Fin 3) :
    leavittWordT (alphaWord i) * (compressionU : BinaryLeavitt) =
      leavittS 0 * leavittWordT (alphaWord i) +
        leavittS 1 * leavittWordT (betaWord i) := by sorry
