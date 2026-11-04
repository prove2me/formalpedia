-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorCoverData_source_controls_w3sum_ac885d1
-- name    : ThreeSum.EncodedColorCoverData.source_controls_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:24:28.061955+00:00
-- url     : https://prove2.me/theorems/1375a0b2-2b63-4d4a-9b1d-6dd7376ca00c
-- title:
--   Encoded Color Cover Data: source controls
-- statement:
--   The Encoded Color Cover Data construction uses the source controls property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorCoverData.lean#L13-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorCoverData.lean#L13-L39

import Definitions.Def_Submission_ThreeSum_SourceFiniteInputs
import Definitions.Def_Submission_ThreeSum_EncodedColorCoverData
set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorCoverData
open Light GlobalEncoding LocalCoverBounds SourceFiniteInputs

theorem ThreeSum.EncodedColorCoverData.source_controls_w3sum_ac885d1 {μ : ℕ → ℤ} {free h J : ℕ} (H : LightCoverKeyData.Stored μ free h J) :
    μ (free+6)=(localPrime h : ℤ) ∧ μ (free+7)=(localBucketCap h : ℤ) ∧
    μ (free+8)=(512*h : ℤ) ∧ μ (free+10)=(scheduleSize h : ℤ) ∧
    μ (free+12)=(maps free h : ℤ) ∧ μ (free+13)=(candidates free h : ℤ) ∧
    μ (free+14)=(leftCounts free h : ℤ) ∧ μ (free+15)=(rightCounts free h : ℤ) := by sorry
