-- Prove2me | Theorems.Thm_ThreeSum_SourceBandPairData_Stored_of_kept_w3sum_ac885d1
-- name    : ThreeSum.SourceBandPairData.Stored.of_kept_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:16:37.090216+00:00
-- url     : https://prove2.me/theorems/5dcdc1ba-1a68-4f91-81aa-8952648a7d2f
-- title:
--   Stored: of kept
-- statement:
--   The Stored construction uses the of kept property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairData.lean#L61-L76
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairData.lean#L61-L76

import Definitions.Def_Submission_ThreeSum_SourceBandData
import Definitions.Def_Submission_ThreeSum_SourceBandPairData
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_ThreeSum_SourceBandData_At_of_kept

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPairData
open Light BandPartition

theorem ThreeSum.SourceBandPairData.Stored.of_kept_w3sum_ac885d1 {μ ν : ℕ → ℤ} {fL fR : ℕ → ℤ}
    {base NL NR g p m bound : ℕ} {shift : ℤ}
    (H : Stored μ fL fR base NL NR g p m shift) (hm : 0 < m)
    (K : Kept μ ν bound) (hb : next base NL NR g m ≤ bound) :
    Stored ν fL fR base NL NR g p m shift := by sorry
