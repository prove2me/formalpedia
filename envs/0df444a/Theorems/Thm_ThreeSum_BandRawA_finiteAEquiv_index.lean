-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_finiteAEquiv_index
-- name    : ThreeSum.BandRawA.finiteAEquiv_index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:06:53.855822+00:00
-- url     : https://prove2.me/theorems/99d3c2be-3a27-48d1-be2d-1459d0bf73d9
-- title:
--   Band Raw A: finite AEquiv index
-- statement:
--   The Band Raw A construction uses the finite AEquiv index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFiniteSlices.lean#L76-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFiniteSlices.lean#L76-L78

import Definitions.Def_Submission_ThreeSum_BandRawAFinite
import Definitions.Def_Submission_ThreeSum_BandRawAFiniteSlices
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
set_option maxHeartbeats 1500000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.finiteAEquiv_index (n g : ℕ) (rs : List Record) (s : ℕ) (hs : s < rs.length)
    (j : Fin (row n g s (rs.getD s default)).length) :
    (finiteAEquiv n g rs s hs j).val.val=count n g rs s+j.val := by sorry
