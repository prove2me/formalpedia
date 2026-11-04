-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_sum_aIndices
-- name    : ThreeSum.BandRawA.sum_aIndices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:28:04.913559+00:00
-- url     : https://prove2.me/theorems/fcbf2ea8-a55d-4298-a365-95324e82c851
-- title:
--   Band Raw A: sum a Indices
-- statement:
--   The Band Raw A construction uses the sum a Indices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAProduct.lean#L114-L118
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAProduct.lean#L114-L118

import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandRawAProduct
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.sum_aIndices (F : ℕ → ℕ) (n g : ℕ) (rs : List Record) (s : ℕ) :
    (∑ k ∈ aIndices n g rs s, F k)=
      ∑ j ∈ range (row n g s (rs.getD s default)).length, F (count n g rs s+j) := by sorry
