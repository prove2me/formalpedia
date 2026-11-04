-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_index_eq_owner_local
-- name    : ThreeSum.BandRawA.index_eq_owner_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:27:10.090192+00:00
-- url     : https://prove2.me/theorems/8b183d5d-d407-4f0f-a25e-a67a8cf3fd04
-- title:
--   Band Raw A: index eq owner local
-- statement:
--   The Band Raw A construction uses the index eq owner local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAIndex.lean#L99-L105
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAIndex.lean#L99-L105

import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Definitions.Def_Submission_ThreeSum_BandRawAIndex
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows
set_option maxHeartbeats 1700000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.index_eq_owner_local {n g k : ℕ} {rs : List Record}
    (hk : k < (items n g rs).length) :
    k=count n g rs (labelAt n g rs k).owner+localA n g rs k := by sorry
