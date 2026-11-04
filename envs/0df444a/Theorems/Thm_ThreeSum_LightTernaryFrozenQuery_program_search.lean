-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryFrozenQuery_program_search
-- name    : ThreeSum.LightTernaryFrozenQuery.program_search
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:32:11.096998+00:00
-- url     : https://prove2.me/theorems/8a7d1180-e1f4-4324-a089-59ac52d8a016
-- title:
--   Light Ternary Frozen Query: program search
-- statement:
--   The Light Ternary Frozen Query construction uses the program search property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQuery.lean#L58-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQuery.lean#L58-L58

import Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQuery
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFrozenQuery
open Light

theorem ThreeSum.LightTernaryFrozenQuery.program_search : program[2]? = some (LightBandLookup.searchBody 2) := by sorry
