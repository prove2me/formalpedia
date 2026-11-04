-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_program_search
-- name    : ThreeSum.LightWeightedFrozenQuery.program_search
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:26:54.597135+00:00
-- url     : https://prove2.me/theorems/9c15ee12-a82b-42a1-b01f-9546ae8a1f20
-- title:
--   Light Weighted Frozen Query: program search
-- statement:
--   The Light Weighted Frozen Query construction uses the program search property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Frozen.lean#L63-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Frozen.lean#L63-L63

import Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_Weighted_Frozen
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedFrozenQuery
open Light

theorem ThreeSum.LightWeightedFrozenQuery.program_search : program[2]? = some (LightBandLookup.searchBody 2) := by sorry
