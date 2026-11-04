-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_sum_bandPositions
-- name    : ThreeSum.BandRawA.sum_bandPositions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:28:14.453794+00:00
-- url     : https://prove2.me/theorems/529dfa7c-0276-4a49-b3a5-ef9afa1aebf3
-- title:
--   Band Raw A: sum band Positions
-- statement:
--   The Band Raw A construction uses the sum band Positions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAProduct.lean#L120-L124
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAProduct.lean#L120-L124

import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandRawAProduct
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.sum_bandPositions (F : ℕ → ℕ) (n g a : ℕ) :
    (∑ p ∈ bandPositions n g a, F p)=
      ∑ j ∈ range (bandLength n g a), F (BandPartition.start g a+j) := by sorry
