-- Prove2me | Theorems.Thm_ThreeSum_LightBandPreprocessing_Output_covers
-- name    : ThreeSum.LightBandPreprocessing.Output.covers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:01:20.392289+00:00
-- url     : https://prove2.me/theorems/025d9f54-0f9b-44b3-b3be-4e1291ae7150
-- title:
--   Output: covers
-- statement:
--   Every original three-set equation reaches a positive stored candidate.
--   The conclusion includes the actual memory interval containing each value.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPreprocessingCorrectness.lean#L47-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPreprocessingCorrectness.lean#L47-L75

import Definitions.Def_Submission_ThreeSum_LightBandPreprocessing
import Definitions.Def_Submission_ThreeSum_BandPreprocessingCorrectness
import Theorems.Thm_ThreeSum_BandPartition_covers
import Theorems.Thm_ThreeSum_LightBandEnumeration_Tables_covers

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPreprocessing
open Light ThreeSum.BandPartition

theorem ThreeSum.LightBandPreprocessing.Output.covers {μ : ℕ → ℤ} {av ae bv be cv ce dst g : ℕ} {hg : 0 < g}
    {originalA originalB originalC : List ℤ} {r x y z : ℤ}
    (h : Output μ av ae bv be cv ce dst g hg originalA originalB originalC r)
    (hx : x ∈ originalA) (hy : y ∈ originalB) (hz : z ∈ originalC) (heq : x+y=z) :
    ∃ i j k, InBand μ ae i x ∧ InBand μ be j y ∧ InBand μ ce k z ∧
      Candidate μ ae be ce dst i j k := by sorry
