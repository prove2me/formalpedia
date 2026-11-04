-- Prove2me | Theorems.Thm_ThreeSum_LightGuardedWanted_program_length
-- name    : ThreeSum.LightGuardedWanted.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:28:04.805973+00:00
-- url     : https://prove2.me/theorems/4464f847-0fc4-4e20-a001-aecfba8a327a
-- title:
--   Light Guarded Wanted: program length
-- statement:
--   The Light Guarded Wanted construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightGuardedWanted.lean#L44-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightGuardedWanted.lean#L44-L44

import Definitions.Def_Submission_ThreeSum_LightCoverKeyData
import Definitions.Def_Submission_ThreeSum_LightRawAKeys
import Definitions.Def_Submission_ThreeSum_LightBalancedWanted
import Definitions.Def_Submission_ThreeSum_LightGuardedWanted
import Theorems.Thm_ThreeSum_LightBalancedWanted_program_length
import Theorems.Thm_ThreeSum_LightCoverKeys_program_length
import Theorems.Thm_ThreeSum_LightGlobalKeys_program_length
import Theorems.Thm_ThreeSum_LightOriginalOffset_program_length
import Theorems.Thm_ThreeSum_LightSourceBucketBuild_program_length
import Theorems.Thm_ThreeSum_LightSourceBucketSetup_program_length
import Theorems.Thm_ThreeSum_LightWantedSetup_program_length

set_option autoImplicit false
open ThreeSum ThreeSum.LightGuardedWanted
open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000

theorem ThreeSum.LightGuardedWanted.program_length : program.length=99 := by sorry
