-- Prove2me | Theorems.Thm_SoficGroups_SourceGeneration_alphaRoot_mem_sourceGenerated
-- name    : SoficGroups.SourceGeneration.alphaRoot_mem_sourceGenerated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.258421+00:00
-- url     : https://prove2.me/theorems/561ee12c-3194-47e6-b922-1495c41e4e6b
-- title:
--   SoficGroups.SourceGeneration.alphaRoot_mem_sourceGenerated
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

theorem SoficGroups.SourceGeneration.alphaRoot_mem_sourceGenerated
    (i j : Fin 3) (hij : i ≠ j) (a : BinaryLeavitt) :
    prefixElementaryUnit alphaPrefixCode i j hij a ∈ sourceGeneratedGroup := by sorry
