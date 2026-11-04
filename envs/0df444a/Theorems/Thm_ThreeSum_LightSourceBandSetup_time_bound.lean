-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBandSetup_time_bound
-- name    : ThreeSum.LightSourceBandSetup.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:24:48.5362+00:00
-- url     : https://prove2.me/theorems/4b62a2b5-4545-4731-91bb-c488b6be8799
-- title:
--   Light Source Band Setup: time bound
-- statement:
--   The Light Source Band Setup construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandSetup.lean#L162-L173
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandSetup.lean#L162-L173

import Definitions.Def_Submission_ThreeSum_LightSourceBandBatch
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightSourceBandSetup
import Theorems.Thm_ThreeSum_LightBlockCoefficients_time_bound
import Theorems.Thm_ThreeSum_LightBlockSourceHashes_time_bound
import Theorems.Thm_ThreeSum_LightDownsetSize_time_bound
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound
import Theorems.Thm_ThreeSum_LightSourceBandBatch_time_bound
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
open ThreeSum ThreeSum.LightSourceBandSetup
open Light BandPartition SourceBandLayout
set_option maxHeartbeats 3000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceBandSetup.time_bound (n g p m U D : ℕ) (hg : 0 < g) :
    time n g p m U D ≤ 1016*n*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+
      size n g*(233*m+1713)+560 := by sorry
