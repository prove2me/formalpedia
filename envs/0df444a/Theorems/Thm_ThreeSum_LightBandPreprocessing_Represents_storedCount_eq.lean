-- Prove2me | Theorems.Thm_ThreeSum_LightBandPreprocessing_Represents_storedCount_eq
-- name    : ThreeSum.LightBandPreprocessing.Represents.storedCount_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:11:30.642209+00:00
-- url     : https://prove2.me/theorems/e7328256-a248-4ad9-b7b2-a28fb9817598
-- title:
--   Represents: stored Count eq
-- statement:
--   The Represents construction uses the stored Count eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPreprocessingCorrectness.lean#L28-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPreprocessingCorrectness.lean#L28-L34

import Definitions.Def_Submission_ThreeSum_LightBandPreprocessing
import Definitions.Def_Submission_ThreeSum_BandPreprocessingCorrectness
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPreprocessing
open Light ThreeSum.BandPartition

theorem ThreeSum.LightBandPreprocessing.Represents.storedCount_eq {μ : ℕ → ℤ} {values endpoints g : ℕ} {hg : 0 < g}
    {original L : List ℤ} {hs : L.Pairwise (· < ·)}
    (h : Represents μ values endpoints g hg original L hs) :
    storedCount μ endpoints = size L.length g := by sorry
