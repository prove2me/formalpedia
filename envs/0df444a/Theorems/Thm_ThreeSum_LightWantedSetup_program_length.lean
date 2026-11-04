-- Prove2me | Theorems.Thm_ThreeSum_LightWantedSetup_program_length
-- name    : ThreeSum.LightWantedSetup.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:08:14.157406+00:00
-- url     : https://prove2.me/theorems/7726f4c3-d154-403c-affc-f94f21c3b8db
-- title:
--   Light Wanted Setup: program length
-- statement:
--   The Light Wanted Setup construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWantedSetup.lean#L54-L54
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWantedSetup.lean#L54-L54

import Definitions.Def_Submission_ThreeSum_LightWantedJoin
import Definitions.Def_Submission_ThreeSum_WantedResidueKeys
import Definitions.Def_Submission_ThreeSum_LightSourceBucketSetup
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_LightWantedSetup
import Theorems.Thm_ThreeSum_LightOriginalOffset_program_length
import Theorems.Thm_ThreeSum_LightSourceBucketBuild_program_length
import Theorems.Thm_ThreeSum_LightSourceBucketSetup_program_length

set_option autoImplicit false
open ThreeSum ThreeSum.LightWantedSetup
open Light WantedResidueKeys
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

theorem ThreeSum.LightWantedSetup.program_length : program.length=12 := by sorry
