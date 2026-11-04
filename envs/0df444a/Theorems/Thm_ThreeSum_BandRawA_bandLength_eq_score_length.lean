-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_bandLength_eq_score_length
-- name    : ThreeSum.BandRawA.bandLength_eq_score_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:28:07.247129+00:00
-- url     : https://prove2.me/theorems/8301821e-ff9f-40a7-b8c0-8a2007f6972b
-- title:
--   Band Raw A: band Length eq score length
-- statement:
--   The Band Raw A construction uses the band Length eq score length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAProduct.lean#L34-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAProduct.lean#L34-L36

import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandRawAProduct
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.bandLength_eq_score_length (n g a : ℕ) :
    bandLength n g a=BandWeightedScore.length n g a := by sorry
