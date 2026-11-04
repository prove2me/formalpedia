-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_items_getD
-- name    : ThreeSum.BandRawA.items_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:33:22.701877+00:00
-- url     : https://prove2.me/theorems/3f42f574-3d82-4ba3-b56a-791a7ecc8df8
-- title:
--   Band Raw A: items get D
-- statement:
--   The Band Raw A construction uses the items get D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAIndex.lean#L56-L59
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAIndex.lean#L56-L59

import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Definitions.Def_Submission_ThreeSum_BandRawAIndex
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows
set_option maxHeartbeats 1700000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.items_getD {n g s j : ℕ} {rs : List Record}
    (hs : s < rs.length) (hj : j < (row n g s (rs.getD s default)).length) :
    labelAt n g rs (count n g rs s+j)=
      ⟨s,BandPartition.start g (rs.getD s default).a+j⟩ := by sorry
