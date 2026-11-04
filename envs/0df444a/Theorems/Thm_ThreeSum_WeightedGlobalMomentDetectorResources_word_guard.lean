-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalMomentDetectorResources_word_guard
-- name    : ThreeSum.WeightedGlobalMomentDetectorResources.word_guard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:25:41.380796+00:00
-- url     : https://prove2.me/theorems/d36b70db-61ee-4d97-8e5d-43d97d1274ae
-- title:
--   Weighted Global Moment Detector Resources: word guard
-- statement:
--   The Weighted Global Moment Detector Resources construction uses the word guard property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentDetectorResources.lean#L123-L126
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentDetectorResources.lean#L123-L126

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryMomentWeightBounds
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_Weighted_Global_TernaryMomentDetectorResources
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalMomentDetectorResources
open WeightedGlobalNativeMomentBounds StageBounds

theorem ThreeSum.WeightedGlobalMomentDetectorResources.word_guard (B U H : ℕ) (lim : Light.Limits)
    (hw : ((need B U H).word : ℤ)≤lim.word) :
    max (input B U H : ℤ) (LightMomentDeterminant.wordBound (input B U H) H)≤lim.word := by sorry
