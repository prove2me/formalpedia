-- Prove2me | Theorems.Thm_SoficGroups_KunExactActualSourceAmbientGenerators_sourceAlphaInclusion_injective
-- name    : SoficGroups.KunExactActualSourceAmbientGenerators.sourceAlphaInclusion_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/e2bf8e7b-1c5b-452d-af7e-ce60d2a68cdc
-- title:
--   SoficGroups.KunExactActualSourceAmbientGenerators.sourceAlphaInclusion_injective
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunExactActualSourceAmbientGenerators
open SoficGroups.KunExactKazhdanGeneratorChange

theorem SoficGroups.KunExactActualSourceAmbientGenerators.sourceAlphaInclusion_injective :
    Function.Injective sourceAlphaInclusion := by sorry
