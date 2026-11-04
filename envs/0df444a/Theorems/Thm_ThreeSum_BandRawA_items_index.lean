-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_items_index
-- name    : ThreeSum.BandRawA.items_index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:33:55.660709+00:00
-- url     : https://prove2.me/theorems/0bb847f9-86a8-47a9-8ec6-93f6a0e489da
-- title:
--   Band Raw A: items index
-- statement:
--   The Band Raw A construction uses the items index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAIndex.lean#L79-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAIndex.lean#L79-L82

import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Definitions.Def_Submission_ThreeSum_BandRawAIndex
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows
set_option maxHeartbeats 1700000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.items_index {n g k : ℕ} {rs : List Record}
    (hk : k < (items n g rs).length) :
    ∃ s < rs.length, ∃ j < (row n g s (rs.getD s default)).length,
      k=count n g rs s+j := by sorry
