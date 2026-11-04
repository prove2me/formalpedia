-- Prove2me | Theorems.Thm_ThreeSum_LightSourceFlagArray_time_bound
-- name    : ThreeSum.LightSourceFlagArray.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:57:14.231883+00:00
-- url     : https://prove2.me/theorems/224d16d3-7e55-4db0-8745-122f8a279ff8
-- title:
--   Light Source Flag Array: time bound
-- statement:
--   The Light Source Flag Array construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceFlagArray.lean#L197-L202
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceFlagArray.lean#L197-L202

import Definitions.Def_Submission_ThreeSum_LightSourceMaskFlags
import Definitions.Def_Submission_ThreeSum_LightSourceFlagArray
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightSourceMaskFlags_time_bound
import Theorems.Thm_ThreeSum_LightSourceRowFlag_time_bound
import Theorems.Thm_ThreeSum_LightSourceTrim_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceFlagArray
open Light SourceFlagProduct
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceFlagArray.time_bound (n J L U : ℕ) :
    time n J L U ≤ n*(300*(J*L+1)^2+
      J*(150*L+464*(Nat.log 2 (L*U+1)+1)+250)+400)+10 := by sorry
