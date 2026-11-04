-- Prove2me | Theorems.Thm_ThreeSum_LightBalancedWanted_time_bound
-- name    : ThreeSum.LightBalancedWanted.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:23:00.781424+00:00
-- url     : https://prove2.me/theorems/85812716-a135-4285-9804-4baf72e460de
-- title:
--   Light Balanced Wanted: time bound
-- statement:
--   The Light Balanced Wanted construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBalancedWanted.lean#L108-L118
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBalancedWanted.lean#L108-L118

import Definitions.Def_Submission_ThreeSum_LightWantedSetup
import Definitions.Def_Submission_ThreeSum_LightBalancedWanted
import Theorems.Thm_ThreeSum_LightBalancedOffset_time_bound
import Theorems.Thm_ThreeSum_LightBlockCoefficients_time_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_time_bound
import Theorems.Thm_ThreeSum_LightLocalKeyRow_time_bound
import Theorems.Thm_ThreeSum_LightLocalKeys_time_bound
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_957e2f25efb6cbcf
import Theorems.Thm_ThreeSum_LightResidueHistogram_time_bound
import Theorems.Thm_ThreeSum_LightSourceBucketBuild_time_bound
import Theorems.Thm_ThreeSum_LightSourceBucketFromHistogram_time_bound
import Theorems.Thm_ThreeSum_LightSourceBucketSetup_time_bound
import Theorems.Thm_ThreeSum_LightSourceResidues_time_bound
import Theorems.Thm_ThreeSum_LightWantedJoin_time_bound
import Theorems.Thm_ThreeSum_LightWantedSetup_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightBalancedWanted
open Light WantedResidueKeys
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits}

theorem ThreeSum.LightBalancedWanted.time_bound (M : ℕ) [NeZero M] (left right : ℕ → ℤ) (NL NR U : ℕ) :
    time M left right NL NR U ≤ LightOriginalOffset.time M NL NR U+
      2000*(NL+NR+M+NL*NR/M+1)*(Nat.log 2 (U+1)+Nat.log 2 (M+M+1)+1)+100 := by sorry
