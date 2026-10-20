-- Prove2me | Theorems.Thm_SoficGroups_SourceGeneration_compressionV_inv_mul_alphaWordS
-- name    : SoficGroups.SourceGeneration.compressionV_inv_mul_alphaWordS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.258421+00:00
-- url     : https://prove2.me/theorems/15cec526-51a9-4429-9dc1-a5feae86410d
-- title:
--   SoficGroups.SourceGeneration.compressionV_inv_mul_alphaWordS
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

theorem SoficGroups.SourceGeneration.compressionV_inv_mul_alphaWordS (i : Fin 3) :
    (↑(compressionV⁻¹) : BinaryLeavitt) * leavittWordS (alphaWord i) =
      leavittWordS (alphaWord i) * leavittT 0 +
        leavittWordS (nuWord i) * leavittT 1 := by sorry
