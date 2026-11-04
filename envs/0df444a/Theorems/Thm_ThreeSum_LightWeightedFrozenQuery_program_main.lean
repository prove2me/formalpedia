-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_program_main
-- name    : ThreeSum.LightWeightedFrozenQuery.program_main
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:40:05.844297+00:00
-- url     : https://prove2.me/theorems/682385c6-babb-494e-aefb-b02cfc5b08b3
-- title:
--   Light Weighted Frozen Query: program main
-- statement:
--   The Light Weighted Frozen Query construction uses the program main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Frozen.lean#L61-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Frozen.lean#L61-L61

import Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_Weighted_Frozen
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedFrozenQuery
open Light

theorem ThreeSum.LightWeightedFrozenQuery.program_main : program[0]? = some (body 0 1 3 4 5) := by sorry
