-- Prove2me | Theorems.Thm_ThreeSum_SourceBandPairData_Data_transfer_w3sum_ac885d1
-- name    : ThreeSum.SourceBandPairData.Data.transfer_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:11:27.276066+00:00
-- url     : https://prove2.me/theorems/834e9660-005c-44c6-88c4-ae641821ee56
-- title:
--   Data: transfer
-- statement:
--   The Data construction uses the transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairData.lean#L37-L59
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairData.lean#L37-L59

import Definitions.Def_Submission_ThreeSum_SourceBandData
import Definitions.Def_Submission_ThreeSum_SourceBandPairData
import Definitions.Def_WeightedCache3SUM_Alias_f1b01b4676766ea6

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPairData
open Light BandPartition

theorem ThreeSum.SourceBandPairData.Data.transfer_w3sum_ac885d1 {μ ν : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g p m : ℕ} {shift : ℤ}
    (H : Data μ fL fR base NL NR g p m shift) (hm : 0 < m)
    (K : ∀ a, leftBase base ≤ a → ν a=μ a) : Data ν fL fR base NL NR g p m shift := by sorry
