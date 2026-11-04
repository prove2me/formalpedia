-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_index_lt_firstRows
-- name    : ThreeSum.BandRawA.index_lt_firstRows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:33:26.471356+00:00
-- url     : https://prove2.me/theorems/8451c6fb-90e3-4cce-bab9-192d9690cc8e
-- title:
--   Band Raw A: index lt first Rows
-- statement:
--   The Band Raw A construction uses the index lt first Rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAIndex.lean#L27-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAIndex.lean#L27-L33

import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Definitions.Def_Submission_ThreeSum_BandRawAIndex
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows
set_option maxHeartbeats 1700000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.index_lt_firstRows {n g s i j : ℕ} {rs : List Record}
    (hs : s < i) (hj : j < (row n g s (rs.getD s default)).length) :
    count n g rs s+j < (firstRows n g rs i).length := by sorry
