-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedNearSource_time_bound
-- name    : ThreeSum.LightWeightedNearSource.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:16:21.891204+00:00
-- url     : https://prove2.me/theorems/3c16d65c-c9ed-49f2-b794-019143b8475d
-- title:
--   Light Weighted Near Source: time bound
-- statement:
--   The entire initialization and memo computation costs only a polynomial in
--   the word dimension and value bit length per actually stored near row.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearSource.lean#L151-L185
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearSource.lean#L151-L185

import Definitions.Def_Submission_Weighted_PhysicalEuler
import Definitions.Def_Submission_Weighted_NearSource
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryDivide_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryRankTable_time_bound
import Theorems.Thm_ThreeSum_LightWeightedEulerMetadata_time_bound
import Theorems.Thm_ThreeSum_LightWeightedPredecessorTable_time_bound
import Theorems.Thm_ThreeSum_LightWeightedPredecessor_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedNearSource
open Light ThreeSum.LightSubsetAddress
open ThreeSum.LightWeightedEulerMetadata
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedNearSource.time_bound {N L rows stages V : ℕ} (hstages : stages≤2*N) :
    time N L rows stages V≤
      11000*(N+L+Nat.log 2 (V+1)+3)^3*(rows+1) := by sorry
