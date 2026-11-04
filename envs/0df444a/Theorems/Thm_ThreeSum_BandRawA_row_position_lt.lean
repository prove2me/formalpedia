-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_row_position_lt
-- name    : ThreeSum.BandRawA.row_position_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:27:02.091888+00:00
-- url     : https://prove2.me/theorems/f6e61e31-1271-4de5-a111-94aa51a1e393
-- title:
--   Band Raw A: row position lt
-- statement:
--   The Band Raw A construction uses the row position lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAMemory.lean#L33-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAMemory.lean#L33-L40

import Definitions.Def_Submission_ThreeSum_LightBandRawARow
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSum_BandRawAMemory
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open Light BandCandidateRows
set_option maxHeartbeats 1400000

theorem ThreeSum.BandRawA.row_position_lt {n g owner j : ℕ} {r : Record}
    (hj : j < (row n g owner r).length) : BandPartition.start g r.a+j < n := by sorry
