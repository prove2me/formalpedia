-- Prove2me | Theorems.Thm_SoficGroups_SourceTopLevelCompressionFinal_binaryLeavittElementaryGroup_not_sofic
-- name    : SoficGroups.SourceTopLevelCompressionFinal.binaryLeavittElementaryGroup_not_sofic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/c9c9acec-8127-4153-a6dd-57b9ce34116f
-- title:
--   SoficGroups.SourceTopLevelCompressionFinal.binaryLeavittElementaryGroup_not_sofic
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceTopLevelCompressionFinal
open SoficGroups.SourceTopLevelCompression
open SoficGroups.KunLiteralNineSourceFiniteModels

theorem SoficGroups.SourceTopLevelCompressionFinal.binaryLeavittElementaryGroup_not_sofic :
    ¬ SoficGroups.Sofic (SoficGroups.binaryLeavittElementaryGroup 9) := by sorry
