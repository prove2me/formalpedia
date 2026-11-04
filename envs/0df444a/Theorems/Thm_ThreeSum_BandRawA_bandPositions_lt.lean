-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_bandPositions_lt
-- name    : ThreeSum.BandRawA.bandPositions_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:37:00.786467+00:00
-- url     : https://prove2.me/theorems/14c58499-9d6f-492e-abe4-4cd27792d930
-- title:
--   Band Raw A: band Positions lt
-- statement:
--   The Band Raw A construction uses the band Positions lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAProduct.lean#L76-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAProduct.lean#L76-L77

import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandRawAProduct
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.bandPositions_lt {n g a p : ℕ} (hp : p ∈ bandPositions n g a) : p < n := by sorry
