-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryEulerMetadata_time_bound
-- name    : ThreeSum.LightTernaryEulerMetadata.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:08:05.564984+00:00
-- url     : https://prove2.me/theorems/f65aa3f4-6956-4cf0-90a6-84b4707efeda
-- title:
--   Light Ternary Euler Metadata: time bound
-- statement:
--   The Light Ternary Euler Metadata construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEulerMetadata.lean#L175-L194
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEulerMetadata.lean#L175-L194

import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessorTable
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMetadata
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPredecessorTable_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPredecessor_time_bound
import Theorems.Thm_ThreeSum_LightTernaryRankTable_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEulerMetadata
open Light ThreeSum.LightSubsetAddress ThreeSum.LightTernaryPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryEulerMetadata.time_bound (N L rows : ℕ) :
    time N L rows≤5000*(N+L+1)^3*(rows+1) := by sorry
