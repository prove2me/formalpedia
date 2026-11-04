-- Prove2me | Theorems.Thm_ThreeSum_BandCandidateRows_fromOwner_of_candidate
-- name    : ThreeSum.BandCandidateRows.fromOwner_of_candidate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:26:43.643469+00:00
-- url     : https://prove2.me/theorems/8c64931c-30af-4593-9e39-dbbfb4a44c67
-- title:
--   Band Candidate Rows: from Owner of candidate
-- statement:
--   The Band Candidate Rows construction uses the from Owner of candidate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandCandidateRows.lean#L177-L206
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandCandidateRows.lean#L177-L206

import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BandCandidateRows
set_option autoImplicit false
open ThreeSum ThreeSum.BandCandidateRows
open BandEnumeration
set_option maxHeartbeats 1400000
set_option maxRecDepth 7000

theorem ThreeSum.BandCandidateRows.fromOwner_of_candidate (A B C : Family) (o : Owner A B C) (t : Triple A B C)
    (hc : candidate A B C o=some t) : fromOwner A B C o=fromTriple t := by sorry
