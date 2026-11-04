-- Prove2me | Theorems.Thm_ThreeSum_SourceFiniteData_Stored_of_kept
-- name    : ThreeSum.SourceFiniteData.Stored.of_kept
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:59:22.26018+00:00
-- url     : https://prove2.me/theorems/bed7d90d-247f-43b4-b50d-61670138f6c8
-- title:
--   Stored: of kept
-- statement:
--   The Stored construction uses the of kept property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorSourceRetention.lean#L23-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorSourceRetention.lean#L23-L32

import Definitions.Def_Submission_ThreeSum_SourceFiniteData
import Definitions.Def_Submission_ThreeSum_EncodedColorSourceRetention
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
open ThreeSum ThreeSum.SourceFiniteData
open Light

theorem ThreeSum.SourceFiniteData.Stored.of_kept {μ ν : ℕ → ℤ} {base g p h J cut bound : ℕ} {B C : List ℤ} {shift r : ℤ}
    (H : Stored μ base g p h J cut B C shift r)
    (K : Kept μ ν bound)
    (hb : LightSourceControlsHost.finish base B.length C.length g h J cut ≤ bound) :
    Stored ν base g p h J cut B C shift r := by sorry
