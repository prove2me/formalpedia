-- Prove2me | Theorems.Thm_ThreeSum_LightWantedJoin_time_bound
-- name    : ThreeSum.LightWantedJoin.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:03:46.5622+00:00
-- url     : https://prove2.me/theorems/53afc8e6-da47-483a-9e42-f56be61fc6b0
-- title:
--   Light Wanted Join: time bound
-- statement:
--   The Light Wanted Join construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWantedJoin.lean#L37-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWantedJoin.lean#L37-L41

import Definitions.Def_Submission_ThreeSum_LightWantedRow
import Definitions.Def_Submission_ThreeSum_WantedPairs
import Definitions.Def_Submission_ThreeSum_LightWantedJoin
import Theorems.Thm_ThreeSum_LightBalancedOffset_time_bound
import Theorems.Thm_ThreeSum_LightBlockCoefficients_time_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_time_bound
import Theorems.Thm_ThreeSum_LightLocalKeyRow_time_bound
import Theorems.Thm_ThreeSum_LightLocalKeys_time_bound
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_957e2f25efb6cbcf
import Theorems.Thm_ThreeSum_LightResidueHistogram_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightWantedJoin
open Light SourceBuckets WantedPairs
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

theorem ThreeSum.LightWantedJoin.time_bound (left right : ℕ → ℕ) (NR n : ℕ) :
    time left right NR n ≤ 400*(n+count left right NR n+1) := by sorry
