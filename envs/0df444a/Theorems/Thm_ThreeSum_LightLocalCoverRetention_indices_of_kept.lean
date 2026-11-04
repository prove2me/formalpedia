-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverRetention_indices_of_kept
-- name    : ThreeSum.LightLocalCoverRetention.indices_of_kept
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:26:57.164999+00:00
-- url     : https://prove2.me/theorems/01815327-e27d-4e41-8638-2b2452c443eb
-- title:
--   Light Local Cover Retention: indices of kept
-- statement:
--   The Light Local Cover Retention construction uses the indices of kept property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverRetention.lean#L44-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverRetention.lean#L44-L51

import Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
import Definitions.Def_Submission_ThreeSum_LightLocalCoverRetention
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverRetention
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMetadata
set_option maxHeartbeats 1000000

theorem ThreeSum.LightLocalCoverRetention.indices_of_kept {μ ν : ℕ → ℤ} {base h : ℕ}
    (H : ∀ s : Occurrence h, μ (candidates base h+s.val) = (candidateAt h s : ℤ))
    (K : Kept μ ν (nextFree base h)) :
    ∀ s : Occurrence h, ν (candidates base h+s.val) = (candidateAt h s : ℤ) := by sorry
