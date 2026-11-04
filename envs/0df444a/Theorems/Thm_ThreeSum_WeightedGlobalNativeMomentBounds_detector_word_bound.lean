-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativeMomentBounds_detector_word_bound
-- name    : ThreeSum.WeightedGlobalNativeMomentBounds.detector_word_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:06:40.471292+00:00
-- url     : https://prove2.me/theorems/eee4503c-c7cc-4ce4-b734-5b0630961658
-- title:
--   Weighted Global Native Moment Bounds: detector word bound
-- statement:
--   The detector's complete arithmetic guard is a fixed polynomial in its
--   explicit input magnitude bound. Its coefficient and degree depend only on H.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeMomentBounds.lean#L184-L200
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeMomentBounds.lean#L184-L200

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativeMomentBounds
open Finset TernaryJointType WeightedGlobalNativePairMoments
open scoped BigOperators

theorem ThreeSum.WeightedGlobalNativeMomentBounds.detector_word_bound (x H : ℕ) :
    max (x : ℤ) (LightMomentDeterminant.wordBound x H)≤(detectorWord x H : ℤ) := by sorry
