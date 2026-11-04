-- Prove2me | Theorems.Thm_ThreeSum_LightWantedSetup_time_bound
-- name    : ThreeSum.LightWantedSetup.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:16:58.860292+00:00
-- url     : https://prove2.me/theorems/b1c880b7-4c90-44a0-855d-4796ae97b8d2
-- title:
--   Light Wanted Setup: time bound
-- statement:
--   The Light Wanted Setup construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWantedSetup.lean#L194-L205
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWantedSetup.lean#L194-L205

import Definitions.Def_Submission_ThreeSum_LightWantedJoin
import Definitions.Def_Submission_ThreeSum_WantedResidueKeys
import Definitions.Def_Submission_ThreeSum_LightSourceBucketSetup
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_LightWantedSetup
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

set_option autoImplicit false
open ThreeSum ThreeSum.LightWantedSetup
open Light WantedResidueKeys
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
variable {lim : Limits}

theorem ThreeSum.LightWantedSetup.time_bound (M : ℕ) (left right : ℕ → ℤ) (NL NR U D : ℕ) (shift : ℤ) :
    time M left right NL NR U D shift ≤
      2000*(NL+NR+M+total M left right NL NR shift+1)*
        (Nat.log 2 (U+1)+Nat.log 2 (M+D+1)+1) := by sorry
