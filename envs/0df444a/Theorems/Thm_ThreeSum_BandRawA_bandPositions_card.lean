-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_bandPositions_card
-- name    : ThreeSum.BandRawA.bandPositions_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:28:59.941506+00:00
-- url     : https://prove2.me/theorems/5bb489d4-1792-4a8f-8dcc-b0405d10c36c
-- title:
--   Band Raw A: band Positions card
-- statement:
--   The Band Raw A construction uses the band Positions card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAScore.lean#L75-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAScore.lean#L75-L78

import Definitions.Def_Submission_ThreeSum_BandRawAProduct
import Definitions.Def_Submission_ThreeSum_BandRawAScore
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.bandPositions_card (n g a : ℕ) :
    (bandPositions n g a).card=bandLength n g a := by sorry
