-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_firstRows_index
-- name    : ThreeSum.BandRawA.firstRows_index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:27:10.707947+00:00
-- url     : https://prove2.me/theorems/cba9f44f-01d7-4f79-ae5c-a6a928b5f5e5
-- title:
--   Band Raw A: first Rows index
-- statement:
--   The Band Raw A construction uses the first Rows index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAIndex.lean#L61-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAIndex.lean#L61-L77

import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Definitions.Def_Submission_ThreeSum_BandRawAIndex
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows
set_option maxHeartbeats 1700000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.firstRows_index {n g i k : ℕ} {rs : List Record}
    (hk : k < (firstRows n g rs i).length) :
    ∃ s < i, ∃ j < (row n g s (rs.getD s default)).length,
      k=count n g rs s+j := by sorry
