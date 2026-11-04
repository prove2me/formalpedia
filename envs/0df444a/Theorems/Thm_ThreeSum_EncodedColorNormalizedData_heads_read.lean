-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorNormalizedData_heads_read
-- name    : ThreeSum.EncodedColorNormalizedData.heads_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:46:19.566339+00:00
-- url     : https://prove2.me/theorems/7c7b3f66-a9e1-4f4a-a582-48b41e42cdf1
-- title:
--   Encoded Color Normalized Data: heads read
-- statement:
--   The Encoded Color Normalized Data construction uses the heads read property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorNormalizedData.lean#L51-L65
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorNormalizedData.lean#L51-L65

import Definitions.Def_Submission_ThreeSum_EncodedColorLayout
import Definitions.Def_Submission_ThreeSum_EncodedColorParameterData
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeCosts
import Definitions.Def_Submission_ThreeSum_EncodedColorNormalizedData
import Theorems.Thm_ThreeSum_EncodedColorPrimeData_Stored_heads_read
import Theorems.Thm_ThreeSum_SourceBandBankData_Stored_heads_read
import Theorems.Thm_ThreeSum_SourceBandPairSlices_heads_read

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorNormalizedData
open Light Scales BandScales ColorClassLists BandRawA EncodedColorLayout

theorem ThreeSum.EncodedColorNormalizedData.heads_read {μ : ℕ → ℤ} {free n g : ℕ} (H : Seg μ free (normalizedHeads free n g)) :
    μ free=(av free n : ℤ) ∧ μ (free+1)=(ae free n : ℤ) ∧
    μ (free+2)=(bv free n : ℤ) ∧ μ (free+3)=(be free n : ℤ) ∧
    μ (free+4)=(cv free n : ℤ) ∧ μ (free+5)=(ce free n : ℤ) ∧
    μ (free+6)=(rec free n g : ℤ) ∧ μ (free+7)=(vals free n g : ℤ) := by sorry
