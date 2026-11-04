-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_mem_aIndices
-- name    : ThreeSum.BandRawA.mem_aIndices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:37:05.470311+00:00
-- url     : https://prove2.me/theorems/54f816e5-168b-43e5-83a0-ccade2b642ba
-- title:
--   Band Raw A: mem a Indices
-- statement:
--   The Band Raw A construction uses the mem a Indices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAProduct.lean#L38-L46
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAProduct.lean#L38-L46

import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandRawAProduct
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.mem_aIndices {n g s k : ℕ} {rs : List Record} :
    k ∈ aIndices n g rs s ↔
      ∃ j < (row n g s (rs.getD s default)).length, k=count n g rs s+j := by sorry
