-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_program_digit
-- name    : ThreeSum.LightWeightedFrozenQuery.program_digit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:26:55.897542+00:00
-- url     : https://prove2.me/theorems/9d07f1c9-3e4a-4ce4-8734-8557f263e9dc
-- title:
--   Light Weighted Frozen Query: program digit
-- statement:
--   The Light Weighted Frozen Query construction uses the program digit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Frozen.lean#L64-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Frozen.lean#L64-L64

import Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_Weighted_Frozen
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedFrozenQuery
open Light

theorem ThreeSum.LightWeightedFrozenQuery.program_digit : program[3]? = some (LightTernaryCodes.digitBody 5) := by sorry
