-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryFrozenQuery_program_main
-- name    : ThreeSum.LightTernaryFrozenQuery.program_main
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:49:57.916429+00:00
-- url     : https://prove2.me/theorems/c84143f0-6ff5-4d5c-b05e-55ff122bfdb1
-- title:
--   Light Ternary Frozen Query: program main
-- statement:
--   The Light Ternary Frozen Query construction uses the program main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQuery.lean#L56-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQuery.lean#L56-L56

import Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQuery
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFrozenQuery
open Light

theorem ThreeSum.LightTernaryFrozenQuery.program_main : program[0]? = some (body 0 1 3 4 5) := by sorry
