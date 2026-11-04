-- Prove2me | Theorems.Thm_ThreeSum_LightSourceMaskFlags_time_bound
-- name    : ThreeSum.LightSourceMaskFlags.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:51:28.7672+00:00
-- url     : https://prove2.me/theorems/a4c5021b-d63d-49eb-b4d1-48a8d96940c0
-- title:
--   Light Source Mask Flags: time bound
-- statement:
--   The Light Source Mask Flags construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceMaskFlags.lean#L147-L153
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceMaskFlags.lean#L147-L153

import Definitions.Def_Submission_ThreeSum_LightSourceTrim
import Definitions.Def_Submission_ThreeSum_LightSourceMaskFlags
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightSourceRowFlag_time_bound
import Theorems.Thm_ThreeSum_LightSourceTrim_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceMaskFlags
open Light SourceFlagProduct
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceMaskFlags.time_bound (J L U : ℕ) :
    time J L U ≤ 300*(J*L+1)^2+
      J*(150*L+464*(Nat.log 2 (L*U+1)+1)+250)+200 := by sorry
