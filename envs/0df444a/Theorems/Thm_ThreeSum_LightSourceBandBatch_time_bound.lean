-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBandBatch_time_bound
-- name    : ThreeSum.LightSourceBandBatch.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:18:03.906094+00:00
-- url     : https://prove2.me/theorems/cbba5a20-3332-480f-ba0e-8c907762d008
-- title:
--   Light Source Band Batch: time bound
-- statement:
--   The Light Source Band Batch construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandBatch.lean#L83-L90
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandBatch.lean#L83-L90

import Definitions.Def_Submission_ThreeSum_LightSourceBandStep
import Definitions.Def_Submission_ThreeSum_LightSourceBandBatch
import Theorems.Thm_ThreeSum_LightBlockCoefficients_time_bound
import Theorems.Thm_ThreeSum_LightBlockSourceHashes_time_bound
import Theorems.Thm_ThreeSum_LightDownsetSize_time_bound
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound
import Theorems.Thm_ThreeSum_LightSourceBucketFromHistogram_time_bound
import Theorems.Thm_ThreeSum_LightSourceBucketOriginal_time_bound
import Theorems.Thm_ThreeSum_LightSourceBuild_time_bound
import Theorems.Thm_ThreeSum_LightSourceGather_time_bound
import Theorems.Thm_ThreeSum_LightSourceHistogram_time_bound
import Theorems.Thm_ThreeSum_LightSourceResidues_time_bound
import Theorems.Thm_ThreeSum_LightSourceRetainedStages_time_bound
import Theorems.Thm_ThreeSum_LightSourceStages_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound
import Theorems.Thm_ThreeSum_LightZetaBatch_time_bound
import Theorems.Thm_ThreeSum_LightZetaCell_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_223d9caf4e7f660b
import Definitions.Def_WeightedCache3SUM_Alias_c2a1891cab57c5b2

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBandBatch
open Light BandPartition SourceBandLayout
set_option maxHeartbeats 2200000
set_option maxRecDepth 16000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceBandBatch.time_bound (n g p m U D : ℕ) (hg : 0 < g) :
    time n g p m U D ≤
      996*n*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+size n g*(233*m+1713)+20 := by sorry
