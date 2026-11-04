-- Prove2me | Theorems.Thm_ThreeSum_LightReportingGatherPair_time_bound
-- name    : ThreeSum.LightReportingGatherPair.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:34:56.117254+00:00
-- url     : https://prove2.me/theorems/a855f892-154a-4869-933e-8ced5f2d347a
-- title:
--   Light Reporting Gather Pair: time bound
-- statement:
--   The Light Reporting Gather Pair construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingGatherPair.lean#L51-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingGatherPair.lean#L51-L53

import Definitions.Def_Submission_ThreeSum_LightReportingGather
import Definitions.Def_Submission_ThreeSum_LightReportingGatherPair
set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingGatherPair
open Light
variable {lim : Limits}

theorem ThreeSum.LightReportingGatherPair.time_bound (t : ℕ) : time t ≤ 80*t+80 := by sorry
