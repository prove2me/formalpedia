-- Prove2me | Theorems.Thm_SoficGroups_SourceGeneration_nineRoot_from_alphaHub_mem_sourceGenerated
-- name    : SoficGroups.SourceGeneration.nineRoot_from_alphaHub_mem_sourceGenerated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.258421+00:00
-- url     : https://prove2.me/theorems/e2b0697f-2f08-491b-bc4c-723d39b8b909
-- title:
--   SoficGroups.SourceGeneration.nineRoot_from_alphaHub_mem_sourceGenerated
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

theorem SoficGroups.SourceGeneration.nineRoot_from_alphaHub_mem_sourceGenerated
    (i : Fin 9) (hi : (0 : Fin 9) ≠ i) (a : BinaryLeavitt) :
    prefixElementaryUnit ninePrefixCode 0 i hi a ∈ sourceGeneratedGroup := by sorry
