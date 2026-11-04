-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryFrozenQuery_program_lookup
-- name    : ThreeSum.LightTernaryFrozenQuery.program_lookup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:31:48.996133+00:00
-- url     : https://prove2.me/theorems/24e3f9cc-c703-45c4-8d92-a2f9e94b30c3
-- title:
--   Light Ternary Frozen Query: program lookup
-- statement:
--   The Light Ternary Frozen Query construction uses the program lookup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQuery.lean#L57-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQuery.lean#L57-L57

import Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQuery
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFrozenQuery
open Light

theorem ThreeSum.LightTernaryFrozenQuery.program_lookup : program[1]? = some (LightTernaryQueryLookup.body 2) := by sorry
