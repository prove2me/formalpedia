-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorWantedData_of_kept
-- name    : ThreeSum.EncodedColorWantedData.of_kept
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:56:10.481562+00:00
-- url     : https://prove2.me/theorems/1d8486a5-7721-41c2-a6e9-e5b7f91a5bd1
-- title:
--   Encoded Color Wanted Data: of kept
-- statement:
--   The Encoded Color Wanted Data construction uses the of kept property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorWantedData.lean#L22-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorWantedData.lean#L22-L32

import Definitions.Def_Submission_ThreeSum_SourceFiniteInputs
import Definitions.Def_Submission_ThreeSum_EncodedColorWantedData
import Theorems.Thm_Light_Seg_of_kept
import Theorems.Thm_ThreeSum_BandRawA_Stored_of_kept
import Definitions.Def_WeightedCache3SUM_Alias_00da40658bb1c003
import Definitions.Def_WeightedCache3SUM_Alias_7dc97c785b0d6c4c
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound
import Definitions.Def_WeightedCache3SUM_Alias_82db098e10427a83
import Definitions.Def_WeightedCache3SUM_Alias_470e48753c64c7fc
import Theorems.Thm_ThreeSum_SourceBandBankLayout_At_of_kept
import Theorems.Thm_ThreeSum_SourceBandData_At_of_kept
import Definitions.Def_WeightedCache3SUM_Alias_78e5c19e1b3827d6

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorWantedData
open Light WantedResidueKeys

theorem ThreeSum.EncodedColorWantedData.of_kept {μ ν : ℕ → ℤ} {out M NL NR bound : ℕ} {left right : ℕ → ℤ} {shift : ℤ}
    (H : LightWantedSetup.Output μ out M left right NL NR shift)
    (K : Kept μ ν bound) (hb : nextFree out M left right NL NR shift ≤ bound) :
    LightWantedSetup.Output ν out M left right NL NR shift := by sorry
