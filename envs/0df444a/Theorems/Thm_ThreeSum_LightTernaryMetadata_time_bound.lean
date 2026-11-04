-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryMetadata_time_bound
-- name    : ThreeSum.LightTernaryMetadata.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:38:50.527991+00:00
-- url     : https://prove2.me/theorems/923a197a-6c0b-4f82-bf1a-a7a0f206bfeb
-- title:
--   Light Ternary Metadata: time bound
-- statement:
--   The Light Ternary Metadata construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMetadata.lean#L174-L177
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMetadata.lean#L174-L177

import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryMetadata
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryMetadata.time_bound (W n : ℕ) : time W n ≤ 1000*(W+1)*(n+1) := by sorry
