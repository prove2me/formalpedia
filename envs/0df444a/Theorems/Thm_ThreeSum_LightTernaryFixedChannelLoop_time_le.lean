-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryFixedChannelLoop_time_le
-- name    : ThreeSum.LightTernaryFixedChannelLoop.time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:03:54.610191+00:00
-- url     : https://prove2.me/theorems/e30a3a6a-debd-4d5a-9f98-62b66285bdb1
-- title:
--   Light Ternary Fixed Channel Loop: time le
-- statement:
--   The Light Ternary Fixed Channel Loop construction uses the time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFixedChannelLoop.lean#L116-L120
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFixedChannelLoop.lean#L116-L120

import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannelStep
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
import Definitions.Def_Submission_ThreeSum_LightTernaryFixedChannelLoop
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFixedChannelLoop
open Light
set_option maxHeartbeats 1500000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryFixedChannelLoop.time_le (terms arity C : ℕ) (cost : Channel→ℕ)
    (hcost : ∀ c∈TernaryMomentSchedule.channels terms, cost c≤C) :
    time (TernaryMomentSchedule.channels terms) cost arity≤terms^2*(arity+2+C) := by sorry
