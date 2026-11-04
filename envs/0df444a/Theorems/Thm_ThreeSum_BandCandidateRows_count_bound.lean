-- Prove2me | Theorems.Thm_ThreeSum_BandCandidateRows_count_bound
-- name    : ThreeSum.BandCandidateRows.count_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:16:18.353562+00:00
-- url     : https://prove2.me/theorems/d66e04c5-6e72-4d51-aa01-e83eeec0ac20
-- title:
--   Band Candidate Rows: count bound
-- statement:
--   The Band Candidate Rows construction uses the count bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandCandidateRows.lean#L213-L220
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandCandidateRows.lean#L213-L220

import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BandCandidateRows
set_option autoImplicit false
open ThreeSum ThreeSum.BandCandidateRows
open BandEnumeration
set_option maxHeartbeats 1400000
set_option maxRecDepth 7000

theorem ThreeSum.BandCandidateRows.count_bound {A B C : Family} {m : ℕ}
    (hA : A.size ≤ m) (hB : B.size ≤ m) (hC : C.size ≤ m) :
    (records A B C).length ≤ 3*m^2 := by sorry
