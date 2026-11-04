-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_program_zero
-- name    : ThreeSum.LightWeightedFrozenQuery.program_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:26:37.526971+00:00
-- url     : https://prove2.me/theorems/4bdcf9ab-f090-4bcf-bf02-814bbc7db513
-- title:
--   Light Weighted Frozen Query: program zero
-- statement:
--   The Light Weighted Frozen Query construction uses the program zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Frozen.lean#L65-L65
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Frozen.lean#L65-L65

import Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_Weighted_Frozen
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedFrozenQuery
open Light

theorem ThreeSum.LightWeightedFrozenQuery.program_zero : program[4]? = some (LightTernaryCodes.zeroBody 5) := by sorry
