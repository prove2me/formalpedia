-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBandStep_original_time_le
-- name    : ThreeSum.LightSourceBandStep.original_time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:33:35.906195+00:00
-- url     : https://prove2.me/theorems/6554bf49-97e3-45dc-8e3b-d2ea68674963
-- title:
--   Light Source Band Step: original time le
-- statement:
--   The Light Source Band Step construction uses the original time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandStep.lean#L48-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandStep.lean#L48-L53

import Definitions.Def_Submission_ThreeSum_SourceBandData
import Definitions.Def_Submission_ThreeSum_LightSourceBandStep
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBandStep
open Light BandPartition SourceBandLayout
set_option maxHeartbeats 3000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceBandStep.original_time_le (n g p m U D i : ℕ) :
    LightSourceBucketOriginal.time (len n g i) p m U D ≤ charge n g p m U D := by sorry
