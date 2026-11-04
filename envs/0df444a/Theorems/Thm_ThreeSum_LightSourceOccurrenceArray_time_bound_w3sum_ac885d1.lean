-- Prove2me | Theorems.Thm_ThreeSum_LightSourceOccurrenceArray_time_bound_w3sum_ac885d1
-- name    : ThreeSum.LightSourceOccurrenceArray.time_bound_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:31:45.472638+00:00
-- url     : https://prove2.me/theorems/357b1074-e6d5-42bd-b720-1e551276c1af
-- title:
--   Light Source Occurrence Array: time bound
-- statement:
--   The Light Source Occurrence Array construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceOccurrenceArray.lean#L96-L109
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceOccurrenceArray.lean#L96-L109

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
import Definitions.Def_Submission_ThreeSum_LightSourceOccurrenceArray
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceOccurrenceArray
open Light OutputDecodeOrder
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceOccurrenceArray.time_bound_w3sum_ac885d1 (N J : ℕ) :
    time N J ≤ 300*(N+1)*(J+1)*(Nat.log 2 (N+1)+2) := by sorry
