-- Prove2me | Theorems.Thm_ThreeSum_LightBandCandidates_time_bound
-- name    : ThreeSum.LightBandCandidates.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:29:12.749374+00:00
-- url     : https://prove2.me/theorems/f3ae247c-5d1c-4444-900e-4d89c632421a
-- title:
--   Light Band Candidates: time bound
-- statement:
--   The Light Band Candidates construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandCandidates.lean#L201-L205
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandCandidates.lean#L201-L205

import Definitions.Def_Submission_ThreeSum_LightBandCandidatesTable
import Definitions.Def_Submission_ThreeSum_LightBandCandidates
import Theorems.Thm_ThreeSum_LightBandEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightBlockCoefficients_time_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_time_bound
import Theorems.Thm_ThreeSum_LightLocalKeyRow_time_bound
import Theorems.Thm_ThreeSum_LightLocalKeys_time_bound
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandCandidates
open Light BandEnumeration BandCandidateRows
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {src dst : ℕ}

theorem ThreeSum.LightBandCandidates.time_bound (a b c : ℕ) :
    time a b c ≤ 1000*(LightBandEnumeration.count a b c+a+b+c+1) := by sorry
