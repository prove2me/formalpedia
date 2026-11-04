-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_valueAt_owner
-- name    : ThreeSum.BandRawA.valueAt_owner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:41:22.761104+00:00
-- url     : https://prove2.me/theorems/f7e17ba4-20fa-4e76-a345-a3fb0f3fdd8e
-- title:
--   Band Raw A: value At owner
-- statement:
--   The Band Raw A construction uses the value At owner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAScore.lean#L22-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAScore.lean#L22-L25

import Definitions.Def_Submission_ThreeSum_BandRawAProduct
import Definitions.Def_Submission_ThreeSum_BandRawAScore
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.valueAt_owner {n g s j : ℕ} {rs : List Record} (A : ℕ → ℤ)
    (hs : s < rs.length) (hj : j < (row n g s (rs.getD s default)).length) :
    valueAt n g rs A (count n g rs s+j)=A (BandPartition.start g (rs.getD s default).a+j) := by sorry
