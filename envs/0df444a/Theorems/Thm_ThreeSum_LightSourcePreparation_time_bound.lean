-- Prove2me | Theorems.Thm_ThreeSum_LightSourcePreparation_time_bound
-- name    : ThreeSum.LightSourcePreparation.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:03:04.638569+00:00
-- url     : https://prove2.me/theorems/e500fab3-bad9-443c-bd35-0c9ce2069fb7
-- title:
--   Light Source Preparation: time bound
-- statement:
--   The Light Source Preparation construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourcePreparation.lean#L163-L169
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourcePreparation.lean#L163-L169

import Definitions.Def_Submission_ThreeSum_LightBlockSourceHashes
import Definitions.Def_Submission_ThreeSum_LightSourceFlagArray
import Definitions.Def_Submission_ThreeSum_LightSourcePreparation
import Theorems.Thm_ThreeSum_LightBlockCoefficients_time_bound
import Theorems.Thm_ThreeSum_LightBlockSourceHashes_time_bound
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound
import Theorems.Thm_ThreeSum_LightSourceFlagArray_time_bound
import Theorems.Thm_ThreeSum_LightSourceMaskFlags_time_bound
import Theorems.Thm_ThreeSum_LightSourceRowFlag_time_bound
import Theorems.Thm_ThreeSum_LightSourceTrim_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourcePreparation
open Light BlockCoefficientRows
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourcePreparation.time_bound (n J L U : ℕ) :
    time n J L U ≤ 300*(J+1)*(L+1)+600*(J*L+1)*(n+1)+
      n*(300*(J*L+1)^2+J*(150*L+464*(Nat.log 2 (L*U+1)+1)+250)+400)+410 := by sorry
