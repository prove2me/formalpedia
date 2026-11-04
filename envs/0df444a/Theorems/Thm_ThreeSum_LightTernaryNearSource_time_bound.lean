-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryNearSource_time_bound
-- name    : ThreeSum.LightTernaryNearSource.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:17:16.508127+00:00
-- url     : https://prove2.me/theorems/c85d90c9-b5b7-4824-a727-adc91581ec51
-- title:
--   Light Ternary Near Source: time bound
-- statement:
--   The entire initialization and memo computation costs only a polynomial in
--   the word dimension and value bit length per actually stored near row.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearSource.lean#L145-L179
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearSource.lean#L145-L179

import Definitions.Def_Submission_ThreeSum_TernaryPhysicalEuler
import Definitions.Def_Submission_ThreeSum_LightTernaryNearSource
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryDivide_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPredecessorTable_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPredecessor_time_bound
import Theorems.Thm_ThreeSum_LightTernaryRankTable_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryNearSource
open Light ThreeSum.LightSubsetAddress
open ThreeSum.LightTernaryEulerMetadata
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryNearSource.time_bound {N L rows stages V : ℕ} (hstages : stages≤2*N) :
    time N L rows stages V≤
      11000*(N+L+Nat.log 2 (V+1)+3)^3*(rows+1) := by sorry
