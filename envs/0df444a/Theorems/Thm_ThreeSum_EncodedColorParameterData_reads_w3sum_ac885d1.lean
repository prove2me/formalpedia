-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorParameterData_reads_w3sum_ac885d1
-- name    : ThreeSum.EncodedColorParameterData.reads_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:34:42.643351+00:00
-- url     : https://prove2.me/theorems/5ea3dafd-ac91-4fe5-95ed-14ca2bf1649d
-- title:
--   Encoded Color Parameter Data: reads
-- statement:
--   The Encoded Color Parameter Data construction uses the reads property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorParameterData.lean#L10-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorParameterData.lean#L10-L28

import Definitions.Def_Submission_ThreeSum_LightParameterInit
import Definitions.Def_Submission_ThreeSum_ColorParameters
import Definitions.Def_Submission_ThreeSum_EncodedColorParameterData
set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorParameterData
open Light Scales BandScales

theorem ThreeSum.EncodedColorParameterData.reads_w3sum_ac885d1 {μ : ℕ → ℤ} {params n : ℕ} (H : Seg μ params (LightParameterInit.values n)) :
    μ params=(inputBits n : ℤ) ∧ μ (params+1)=(microHalf (inputBits n) : ℤ) ∧
    μ (params+3)=(blockCount (inputBits n) : ℤ) ∧ μ (params+4)=(mu n : ℤ) ∧
    μ (params+14)=(radix n : ℤ) ∧ μ (params+17)=(bandSize n : ℤ) ∧
    μ (params+18)=(primeWindow n : ℤ) := by sorry
