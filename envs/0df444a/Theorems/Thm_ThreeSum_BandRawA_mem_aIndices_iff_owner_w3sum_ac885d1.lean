-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_mem_aIndices_iff_owner_w3sum_ac885d1
-- name    : ThreeSum.BandRawA.mem_aIndices_iff_owner_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:28:22.810192+00:00
-- url     : https://prove2.me/theorems/d9191351-0d97-4d3d-b2a2-61f795a0f831
-- title:
--   Band Raw A: mem a Indices iff owner
-- statement:
--   The Band Raw A construction uses the mem a Indices iff owner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAProduct.lean#L48-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAProduct.lean#L48-L61

import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandRawAProduct
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.mem_aIndices_iff_owner_w3sum_ac885d1 {n g s k : ℕ} {rs : List Record} (hs : s < rs.length) :
    k ∈ aIndices n g rs s ↔
      k < (items n g rs).length ∧ (labelAt n g rs k).owner=s := by sorry
