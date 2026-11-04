-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorPipelineData_ordered_w3sum_ac885d1
-- name    : ThreeSum.EncodedColorPipelineData.ordered_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:58:30.402202+00:00
-- url     : https://prove2.me/theorems/a45680de-8298-4072-bb2a-40936d4b4ce5
-- title:
--   Encoded Color Pipeline Data: ordered
-- statement:
--   The Encoded Color Pipeline Data construction uses the ordered property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPipelineData.lean#L82-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPipelineData.lean#L82-L107

import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeReadyData
import Definitions.Def_Submission_ThreeSum_LightEncodedColorWantedSources
import Definitions.Def_Submission_ThreeSum_LightEncodedColorResult
import Definitions.Def_Submission_ThreeSum_EncodedColorPipelineData
import Theorems.Thm_ThreeSum_SourceBandPairData_ordered

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorPipelineData
open Light Scales BandScales ColorClassLists EncodedColorNormalizedData
attribute [local instance] ThreeSum.EncodedColorPipelineData._p2m_local_instance_be6b5e3d97_11

theorem ThreeSum.EncodedColorPipelineData.ordered_w3sum_ac885d1 (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    EncodedColorLayout.prime free n (bandSize n)+6 ≤ coverBase free n ∧
    free+8 ≤ coverBase free n ∧ coverBase free n ≤ controls free n A B C hsA hsB hsC ∧
    wantedHeader free n (incidences n A B C hsA hsB hsC).length+4 ≤ controls free n A B C hsA hsB hsC ∧
    controls free n A B C hsA hsB hsC+3 ≤ finish free n A B C hsA hsB hsC ∧
    bankHeader free n A B C hsA hsB hsC+5 ≤ finish free n A B C hsA hsB hsC := by sorry
