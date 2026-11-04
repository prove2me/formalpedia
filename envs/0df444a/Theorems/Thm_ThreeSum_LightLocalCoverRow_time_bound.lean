-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverRow_time_bound
-- name    : ThreeSum.LightLocalCoverRow.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:38:11.868415+00:00
-- url     : https://prove2.me/theorems/dcc71531-b224-4f50-ba74-a2c0162cf125
-- title:
--   Light Local Cover Row: time bound
-- statement:
--   The Light Local Cover Row construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverRow.lean#L114-L117
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverRow.lean#L114-L117

import Definitions.Def_Submission_ThreeSum_LightPairFlags
import Definitions.Def_Submission_ThreeSum_LightSupportMark
import Definitions.Def_Submission_ThreeSum_LightLocalCoverRow
import Theorems.Thm_ThreeSum_LightPairFlags_time_bound
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverRow
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightLocalCoverRow.time_bound (L n p : ℕ) : time L n p ≤ 600*(n*n+1)*(L+n+p*p+1) := by sorry
