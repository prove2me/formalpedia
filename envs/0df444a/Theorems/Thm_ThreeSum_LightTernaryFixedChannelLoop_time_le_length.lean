-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryFixedChannelLoop_time_le_length
-- name    : ThreeSum.LightTernaryFixedChannelLoop.time_le_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:03:57.355824+00:00
-- url     : https://prove2.me/theorems/1b59e5af-6928-4f81-b6a6-3bfeb7b6b38b
-- title:
--   Light Ternary Fixed Channel Loop: time le length
-- statement:
--   The number of complete source-count calls is a fixed quadratic in the
--   chosen moment count, independent of the original input size.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFixedChannelLoop.lean#L105-L114
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFixedChannelLoop.lean#L105-L114

import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannelStep
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
import Definitions.Def_Submission_ThreeSum_LightTernaryFixedChannelLoop
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFixedChannelLoop
open Light
set_option maxHeartbeats 1500000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryFixedChannelLoop.time_le_length (steps : List Channel) (arity C : ℕ) (cost : Channel→ℕ)
    (hcost : ∀ c∈steps, cost c≤C) :
    time steps cost arity≤steps.length*(arity+2+C) := by sorry
