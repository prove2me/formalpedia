-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorResources_schedule_power_le_w3sum_ac885d1
-- name    : ThreeSum.EncodedColorResources.schedule_power_le_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:41:08.328517+00:00
-- url     : https://prove2.me/theorems/e29e7890-fddb-46dc-ad53-906d2fce9227
-- title:
--   Encoded Color Resources: schedule power le
-- statement:
--   The Encoded Color Resources construction uses the schedule power le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorResourceScale.lean#L80-L91
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorResourceScale.lean#L80-L91

import Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts
import Definitions.Def_Submission_ThreeSum_LightBandRawAResourcesScales
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
import Definitions.Def_Submission_ThreeSum_EncodedColorResourceScale
set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorResources
open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open Filter
set_option maxHeartbeats 2200000
set_option maxRecDepth 13000

theorem ThreeSum.EncodedColorResources.schedule_power_le_w3sum_ac885d1 (n : ℕ) : (scheduleSize (half n)+1)^(blocks n+1) ≤ 2*(scale n)^3 := by sorry
