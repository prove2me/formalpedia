-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBuild_time_bound
-- name    : ThreeSum.LightSourceBuild.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:47:58.133127+00:00
-- url     : https://prove2.me/theorems/cd31b16d-ec96-4ce1-bee2-d7469b408439
-- title:
--   Light Source Build: time bound
-- statement:
--   The Light Source Build construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBuild.lean#L141-L148
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBuild.lean#L141-L148

import Definitions.Def_Submission_ThreeSum_LightSourceGather
import Definitions.Def_Submission_ThreeSum_LightSourceBuild
import Theorems.Thm_ThreeSum_LightSourceGather_time_bound
import Theorems.Thm_ThreeSum_LightSourceHistogram_time_bound
import Theorems.Thm_ThreeSum_LightSourceResidues_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBuild
open Light
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceBuild.time_bound (N n p m U D E : ℕ) :
    time N n p m U D E ≤
      278*N*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+
      157*n*(Nat.log 2 (E+1)+1)+13*m+169 := by sorry
