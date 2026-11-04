-- Prove2me | Theorems.Thm_ThreeSum_LightBalancedWanted_program_length
-- name    : ThreeSum.LightBalancedWanted.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:18:15.244781+00:00
-- url     : https://prove2.me/theorems/6a6a39f7-f4f5-4b78-9076-ac869b60bd90
-- title:
--   Light Balanced Wanted: program length
-- statement:
--   The Light Balanced Wanted construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBalancedWanted.lean#L28-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBalancedWanted.lean#L28-L28

import Definitions.Def_Submission_ThreeSum_LightWantedSetup
import Definitions.Def_Submission_ThreeSum_LightBalancedWanted
import Theorems.Thm_ThreeSum_LightOriginalOffset_program_length
import Theorems.Thm_ThreeSum_LightSourceBucketBuild_program_length
import Theorems.Thm_ThreeSum_LightSourceBucketSetup_program_length
import Theorems.Thm_ThreeSum_LightWantedSetup_program_length

set_option autoImplicit false
open ThreeSum ThreeSum.LightBalancedWanted
open Light WantedResidueKeys
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

theorem ThreeSum.LightBalancedWanted.program_length : program.length=26 := by sorry
