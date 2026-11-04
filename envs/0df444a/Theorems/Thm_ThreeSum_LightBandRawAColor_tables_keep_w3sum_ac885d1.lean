-- Prove2me | Theorems.Thm_ThreeSum_LightBandRawAColor_tables_keep_w3sum_ac885d1
-- name    : ThreeSum.LightBandRawAColor.tables_keep_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:28:56.716419+00:00
-- url     : https://prove2.me/theorems/d34a5450-eb8c-420d-8cde-791728f1181f
-- title:
--   Light Band Raw AColor: tables keep
-- statement:
--   The Light Band Raw AColor construction uses the tables keep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawAColor.lean#L63-L80
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawAColor.lean#L63-L80

import Definitions.Def_Submission_ThreeSum_LightColorBands
import Definitions.Def_Submission_ThreeSum_LightBandRawACatalog
import Definitions.Def_Submission_ThreeSum_BandRawAOriginal
import Definitions.Def_Submission_ThreeSum_LightBandRawAColor
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawAColor
open Light BandPartition BandCandidateRows BandRawA ColorClassLists
set_option maxHeartbeats 2400000
set_option maxRecDepth 11000

theorem ThreeSum.LightBandRawAColor.tables_keep_w3sum_ac885d1 {μ ν : ℕ → ℤ} {tables bound : ℕ} {A B C : BandEnumeration.Family}
    (ht : LightBandEnumeration.Tables μ tables A B C) (hk : Kept μ ν bound)
    (hb : tables+LightBandEnumeration.count A.size B.size C.size ≤ bound) :
    LightBandEnumeration.Tables ν tables A B C := by sorry
