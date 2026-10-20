-- Prove2me | Theorems.Thm_SoficGroups_KunExactActualSourceAmbientGenerators_range_sourcePositiveGeneratorMap
-- name    : SoficGroups.KunExactActualSourceAmbientGenerators.range_sourcePositiveGeneratorMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/264d773a-6617-45fd-af2c-123002b16da2
-- title:
--   SoficGroups.KunExactActualSourceAmbientGenerators.range_sourcePositiveGeneratorMap
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunExactActualSourceAmbientGenerators

theorem SoficGroups.KunExactActualSourceAmbientGenerators.range_sourcePositiveGeneratorMap
    (SΓ : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode)) :
    Set.range (sourcePositiveGeneratorMap SΓ) =
      (sourcePositiveGenerators SΓ : Set
        (SoficGroups.prefixElementaryGroup
          SoficGroups.ninePrefixCode)) := by sorry
