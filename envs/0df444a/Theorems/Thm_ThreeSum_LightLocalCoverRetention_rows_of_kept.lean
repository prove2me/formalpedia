-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverRetention_rows_of_kept
-- name    : ThreeSum.LightLocalCoverRetention.rows_of_kept
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:07.031493+00:00
-- url     : https://prove2.me/theorems/acb1ad9b-3d11-4ba1-8df3-654d5d14d2ef
-- title:
--   Light Local Cover Retention: rows of kept
-- statement:
--   The Light Local Cover Retention construction uses the rows of kept property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverRetention.lean#L34-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverRetention.lean#L34-L42

import Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
import Definitions.Def_Submission_ThreeSum_LightLocalCoverRetention
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverRetention
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMetadata
set_option maxHeartbeats 1000000

theorem ThreeSum.LightLocalCoverRetention.rows_of_kept {μ ν : ℕ → ℤ} {base h : ℕ}
    (H : ScheduleRows μ h (scheduleMaps base h))
    (K : Kept μ ν (nextFree base h)) :
    ScheduleRows ν h (scheduleMaps base h) := by sorry
