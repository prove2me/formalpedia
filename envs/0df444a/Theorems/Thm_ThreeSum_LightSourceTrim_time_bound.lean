-- Prove2me | Theorems.Thm_ThreeSum_LightSourceTrim_time_bound
-- name    : ThreeSum.LightSourceTrim.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:44:34.465702+00:00
-- url     : https://prove2.me/theorems/0eaaf66b-1ac0-43e2-8060-b240eed6d9ae
-- title:
--   Light Source Trim: time bound
-- statement:
--   The Light Source Trim construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceTrim.lean#L240-L244
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceTrim.lean#L240-L244

import Definitions.Def_Submission_ThreeSum_LightSourceRowFlag
import Definitions.Def_Submission_ThreeSum_SourceFlagProduct
import Definitions.Def_Submission_ThreeSum_LightSourceTrim
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightSourceRowFlag_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceTrim
open Light SourceFlagProduct
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceTrim.time_bound (J L U : ℕ) :
    time J L U ≤ J*(150*L+464*(Nat.log 2 (L*U+1)+1)+250)+100 := by sorry
