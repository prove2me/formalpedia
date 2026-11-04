-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCounts_time_bound
-- name    : ThreeSum.LightLocalCounts.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:37:11.705131+00:00
-- url     : https://prove2.me/theorems/90c00e34-9e45-4f94-ac9a-e32f2a4a694f
-- title:
--   Light Local Counts: time bound
-- statement:
--   The Light Local Counts construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCounts.lean#L194-L198
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCounts.lean#L194-L198

import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCounts
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCounts
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open Light LocalCoverBounds LightPascal LightSubsetAddress
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightLocalCounts.time_bound (h : ℕ) : time h ≤ 1700*(512*h+1)^2 := by sorry
