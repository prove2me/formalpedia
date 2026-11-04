-- Prove2me | Theorems.Thm_ThreeSum_SourceBandPairSlices_heads_read
-- name    : ThreeSum.SourceBandPairSlices.heads_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:02:36.294609+00:00
-- url     : https://prove2.me/theorems/dc2b0329-da4f-45e8-ad79-7d197229b708
-- title:
--   Source Band Pair Slices: heads read
-- statement:
--   The Source Band Pair Slices construction uses the heads read property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairSlices.lean#L62-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairSlices.lean#L62-L75

import Definitions.Def_Submission_ThreeSum_SourceBandPairData
import Definitions.Def_Submission_ThreeSum_SourceBandPartition
import Definitions.Def_Submission_ThreeSum_SourceBandPairSlices
import Theorems.Thm_Light_Ends_next

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPairSlices
open Light BandPartition SourceBandLayout SourceBandPairData

theorem ThreeSum.SourceBandPairSlices.heads_read {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g p m : ℕ} {shift : ℤ}
    (H : Stored μ fL fR base NL NR g p m shift) :
    μ base=(leftBase base : ℤ) ∧ μ (base+1)=(size NL g : ℤ) ∧
    μ (base+2)=(rightBase base NL g m : ℤ) ∧ μ (base+3)=(size NR g : ℤ) ∧
    μ (base+4)=(zeroBase base NL NR g m : ℤ) ∧ μ (base+5)=(next base NL NR g m : ℤ) ∧
    μ (base+6)=(NL : ℤ) ∧ μ (base+7)=(NR : ℤ) := by sorry
