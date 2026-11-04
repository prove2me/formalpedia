-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_mem_bandPositions
-- name    : ThreeSum.BandRawA.mem_bandPositions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:37:30.412114+00:00
-- url     : https://prove2.me/theorems/68407641-4c0f-4e7e-b0aa-93904839a700
-- title:
--   Band Raw A: mem band Positions
-- statement:
--   The Band Raw A construction uses the mem band Positions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAProduct.lean#L63-L74
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAProduct.lean#L63-L74

import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandRawAProduct
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.mem_bandPositions {n g a p : ℕ} :
    p ∈ bandPositions n g a ↔
      BandPartition.start g a ≤ p ∧ p < BandPartition.stop n g a := by sorry
