-- Prove2me | Theorems.Thm_ThreeSum_BandCandidateRows_rect_getD
-- name    : ThreeSum.BandCandidateRows.rect_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:16:27.89277+00:00
-- url     : https://prove2.me/theorems/213cf7d5-421f-46f0-9f91-603c4b8e77d3
-- title:
--   Band Candidate Rows: rect get D
-- statement:
--   The Band Candidate Rows construction uses the rect get D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandCandidateRows.lean#L88-L96
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandCandidateRows.lean#L88-L96

import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BandCandidateRows
set_option autoImplicit false
open ThreeSum ThreeSum.BandCandidateRows
open BandEnumeration
set_option maxHeartbeats 1400000
set_option maxRecDepth 7000

theorem ThreeSum.BandCandidateRows.rect_getD {m n i j : ℕ} (F : ℕ → ℕ → Record) (hi : i < m) (hj : j < n) :
    (rect m n F).getD (i*n+j) default=F i j := by sorry
