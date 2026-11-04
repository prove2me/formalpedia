-- Prove2me | Theorems.Thm_ThreeSum_LightRadixRows_time_bound
-- name    : ThreeSum.LightRadixRows.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:28:45.248007+00:00
-- url     : https://prove2.me/theorems/973ce843-afaa-4428-a88c-a92e2f5364ba
-- title:
--   Light Radix Rows: time bound
-- statement:
--   The Light Radix Rows construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRadixRows.lean#L138-L140
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRadixRows.lean#L138-L140

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_LightRadixRows
set_option autoImplicit false
open ThreeSum ThreeSum.LightRadixRows
open Light RadixKeyLists
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightRadixRows.time_bound (m n : ℕ) : time m n ≤ 130*(m+1)*(n+1) := by sorry
