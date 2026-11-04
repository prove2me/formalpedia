-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_finiteBandPositions_card
-- name    : ThreeSum.BandRawA.finiteBandPositions_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:33:24.907252+00:00
-- url     : https://prove2.me/theorems/9653fa90-5ef7-4d2a-9005-09cb0231f6c6
-- title:
--   Band Raw A: finite Band Positions card
-- statement:
--   The Band Raw A construction uses the finite Band Positions card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFiniteSlices.lean#L49-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFiniteSlices.lean#L49-L51

import Definitions.Def_Submission_ThreeSum_BandRawAFinite
import Definitions.Def_Submission_ThreeSum_BandRawAFiniteSlices
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
set_option maxHeartbeats 1500000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.finiteBandPositions_card (n g a : ℕ) :
    (finiteBandPositions n g a).card=bandLength n g a := by sorry
