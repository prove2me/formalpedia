-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_localA_lt
-- name    : ThreeSum.BandRawA.localA_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:05:20.289881+00:00
-- url     : https://prove2.me/theorems/b8590f67-3437-4be2-be1b-95d2a55c2a29
-- title:
--   Band Raw A: local A lt
-- statement:
--   The Band Raw A construction uses the local A lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAIndex.lean#L107-L112
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAIndex.lean#L107-L112

import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Definitions.Def_Submission_ThreeSum_BandRawAIndex
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows
set_option maxHeartbeats 1700000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.localA_lt {n g k : ℕ} {rs : List Record}
    (hk : k < (items n g rs).length) :
    localA n g rs k < bandLength n g (ownerRecord n g rs k).a := by sorry
