-- Prove2me | Theorems.Thm_ThreeSum_LightBandPreprocessing_Output_count_bound
-- name    : ThreeSum.LightBandPreprocessing.Output.count_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:01:24.689196+00:00
-- url     : https://prove2.me/theorems/b3383b5a-0fec-412f-9e96-daed8c05572d
-- title:
--   Output: count bound
-- statement:
--   The Output construction uses the count bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPreprocessingCorrectness.lean#L77-L85
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPreprocessingCorrectness.lean#L77-L85

import Definitions.Def_Submission_ThreeSum_LightBandPreprocessing
import Definitions.Def_Submission_ThreeSum_BandPreprocessingCorrectness
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPreprocessing
open Light ThreeSum.BandPartition

theorem ThreeSum.LightBandPreprocessing.Output.count_bound {μ : ℕ → ℤ} {av ae bv be cv ce dst g : ℕ} {hg : 0 < g}
    {originalA originalB originalC : List ℤ} {r : ℤ}
    (h : Output μ av ae bv be cv ce dst g hg originalA originalB originalC r) :
    0 ≤ r ∧ r ≤ (LightBandEnumeration.count (size originalA.length g)
      (size originalB.length g) (size originalC.length g) : ℤ) := by sorry
