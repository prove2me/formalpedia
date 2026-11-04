-- Prove2me | Theorems.Thm_ThreeSum_LightSwitchDepth_time_bound
-- name    : ThreeSum.LightSwitchDepth.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:12:47.506053+00:00
-- url     : https://prove2.me/theorems/9abde9b8-ef91-4f7a-aba3-5d671b0a09c9
-- title:
--   Light Switch Depth: time bound
-- statement:
--   The Light Switch Depth construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitchDepth.lean#L43-L46
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitchDepth.lean#L43-L46

import Definitions.Def_Submission_ThreeSum_LightSwitch
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitchDepth
open Light
variable {lim : Limits} {P : Program} {μ : ℕ→ℤ} {J d : ℕ}

theorem ThreeSum.LightSwitchDepth.time_bound (J : ℕ) : time J ≤ 260*J+90 := by sorry
