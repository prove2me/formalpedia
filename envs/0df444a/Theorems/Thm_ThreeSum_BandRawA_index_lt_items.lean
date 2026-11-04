-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_index_lt_items
-- name    : ThreeSum.BandRawA.index_lt_items
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:33:14.942844+00:00
-- url     : https://prove2.me/theorems/a4dfeb8c-dbde-42ec-ad04-692225cfc655
-- title:
--   Band Raw A: index lt items
-- statement:
--   The Band Raw A construction uses the index lt items property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAIndex.lean#L35-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAIndex.lean#L35-L37

import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Definitions.Def_Submission_ThreeSum_BandRawAIndex
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows
set_option maxHeartbeats 1700000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.index_lt_items {n g s j : ℕ} {rs : List Record}
    (hs : s < rs.length) (hj : j < (row n g s (rs.getD s default)).length) :
    count n g rs s+j < (items n g rs).length := by sorry
