-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativeMomentBounds_detector_moments_bound
-- name    : ThreeSum.WeightedGlobalNativeMomentBounds.detector_moments_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:06:05.200043+00:00
-- url     : https://prove2.me/theorems/c2db8d27-ccfa-4645-a56b-0fac12a77835
-- title:
--   Weighted Global Native Moment Bounds: detector moments bound
-- statement:
--   The Weighted Global Native Moment Bounds construction uses the detector moments bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeMomentBounds.lean#L202-L207
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeMomentBounds.lean#L202-L207

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativeMomentBounds
open Finset TernaryJointType WeightedGlobalNativePairMoments
open scoped BigOperators

theorem ThreeSum.WeightedGlobalNativeMomentBounds.detector_moments_bound {N U H : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (B C : ℕ→ℤ) (hB : ∀ j<S.left.NL, |B j|≤(U : ℤ))
    (hC : ∀ j<S.right.NL, |C j|≤(U : ℤ)) :
    ∀ i, ∀ k≤2*H, |∑ p : Pair S i, mass S i p*mode B C p^k|≤(detectorInput S U H : ℤ) := by sorry
