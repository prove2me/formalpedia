-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedEulerMetadata_time_bound
-- name    : ThreeSum.LightWeightedEulerMetadata.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:08:19.066229+00:00
-- url     : https://prove2.me/theorems/0d74d813-9dd7-4ea6-9878-cec160e393be
-- title:
--   Light Weighted Euler Metadata: time bound
-- statement:
--   The Light Weighted Euler Metadata construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/EulerMetadata.lean#L180-L199
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/EulerMetadata.lean#L180-L199

import Definitions.Def_Submission_Weighted_PredecessorTable
import Definitions.Def_Submission_Weighted_EulerMetadata
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryRankTable_time_bound
import Theorems.Thm_ThreeSum_LightWeightedPredecessorTable_time_bound
import Theorems.Thm_ThreeSum_LightWeightedPredecessor_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedEulerMetadata
open Light ThreeSum.LightSubsetAddress ThreeSum.LightWeightedPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedEulerMetadata.time_bound (N L rows : ℕ) :
    time N L rows≤5000*(N+L+1)^3*(rows+1) := by sorry
