-- Prove2me | Theorems.Thm_ThreeSum_LightBandPreprocessing_time_bound_w3sum_ac885d1
-- name    : ThreeSum.LightBandPreprocessing.time_bound_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:12:45.214859+00:00
-- url     : https://prove2.me/theorems/14c6891b-23c3-446f-85bc-888bd96af733
-- title:
--   Light Band Preprocessing: time bound
-- statement:
--   The Light Band Preprocessing construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPreprocessingCorrectness.lean#L87-L111
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPreprocessingCorrectness.lean#L87-L111

import Definitions.Def_Submission_ThreeSum_LightBandPreprocessing
import Definitions.Def_Submission_ThreeSum_BandPreprocessingCorrectness
import Theorems.Thm_ThreeSum_LightBandEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightBandPartition_time_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_time_bound
import Theorems.Thm_ThreeSum_LightNormalize_time_bound
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound
import Theorems.Thm_ThreeSum_LightSortedBands_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPreprocessing
open Light ThreeSum.BandPartition

theorem ThreeSum.LightBandPreprocessing.time_bound_w3sum_ac885d1 (a b c g : ℕ) :
    time a b c g ≤
      2100*(a+b+c+1)*(Nat.clog 2 (a+b+c)+1)+
      1000*(LightBandEnumeration.count (size a g) (size b g) (size c g)+a+b+c+1)*
        (LightBandEnumeration.width (size a g) (size b g) (size c g)+1)+400 := by sorry
