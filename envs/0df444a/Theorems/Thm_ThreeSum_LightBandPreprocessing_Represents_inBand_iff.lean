-- Prove2me | Theorems.Thm_ThreeSum_LightBandPreprocessing_Represents_inBand_iff
-- name    : ThreeSum.LightBandPreprocessing.Represents.inBand_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:11:34.158165+00:00
-- url     : https://prove2.me/theorems/5a8c8900-c5ba-49f7-9e8f-ce091d3d0e4e
-- title:
--   Represents: in Band iff
-- statement:
--   The Represents construction uses the in Band iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPreprocessingCorrectness.lean#L36-L43
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPreprocessingCorrectness.lean#L36-L43

import Definitions.Def_Submission_ThreeSum_LightBandPreprocessing
import Definitions.Def_Submission_ThreeSum_BandPreprocessingCorrectness
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPreprocessing
open Light ThreeSum.BandPartition

theorem ThreeSum.LightBandPreprocessing.Represents.inBand_iff {μ : ℕ → ℤ} {values endpoints g i : ℕ} {hg : 0 < g}
    {original L : List ℤ} {hs : L.Pairwise (· < ·)} {z : ℤ}
    (h : Represents μ values endpoints g hg original L hs) (hi : i < size L.length g) :
    InBand μ endpoints i z ↔
      L.getD (start g i) 0 ≤ z ∧ z ≤ L.getD (stop L.length g i-1) 0 := by sorry
