-- Prove2me | Theorems.Thm_ThreeSum_LightSourceRowFlag_time_bound
-- name    : ThreeSum.LightSourceRowFlag.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:38:53.301552+00:00
-- url     : https://prove2.me/theorems/6b5aa200-9db3-4fdb-b569-e976d9ac77b6
-- title:
--   Light Source Row Flag: time bound
-- statement:
--   The Light Source Row Flag construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceRowFlag.lean#L167-L170
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceRowFlag.lean#L167-L170

import Definitions.Def_Submission_ThreeSum_LightSourceRowScan
import Definitions.Def_Submission_ThreeSum_LightSourceFlagTest
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightSourceRowFlag
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceRowFlag
open Light
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceRowFlag.time_bound (L U : ℕ) :
    time L U ≤ 150*L+464*(Nat.log 2 (L*U+1)+1) := by sorry
