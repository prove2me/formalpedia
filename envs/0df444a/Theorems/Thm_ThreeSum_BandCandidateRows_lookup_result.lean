-- Prove2me | Theorems.Thm_ThreeSum_BandCandidateRows_lookup_result
-- name    : ThreeSum.BandCandidateRows.lookup_result
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:26:41.317249+00:00
-- url     : https://prove2.me/theorems/0ed066ff-f3bd-4089-b37e-7f22e4b44f83
-- title:
--   Band Candidate Rows: lookup result
-- statement:
--   The Band Candidate Rows construction uses the lookup result property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandCandidateRows.lean#L173-L175
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandCandidateRows.lean#L173-L175

import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BandCandidateRows
set_option autoImplicit false
open ThreeSum ThreeSum.BandCandidateRows
open BandEnumeration
set_option maxHeartbeats 1400000
set_option maxRecDepth 7000

theorem ThreeSum.BandCandidateRows.lookup_result (A : Family) (x : ℤ) (i : A.Index) (hi : A.lookup x=some i) :
    LightBandLookup.result A.lower A.upper A.size x=i.val+1 := by sorry
