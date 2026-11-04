-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativeMomentBounds_moment_abs_le
-- name    : ThreeSum.WeightedGlobalNativeMomentBounds.moment_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:06:45.848202+00:00
-- url     : https://prove2.me/theorems/d2e768ef-4af9-49a9-bc1c-c74b3b958c5b
-- title:
--   Weighted Global Native Moment Bounds: moment abs le
-- statement:
--   The Weighted Global Native Moment Bounds construction uses the moment abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeMomentBounds.lean#L76-L102
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeMomentBounds.lean#L76-L102

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativeMomentBounds
open Finset TernaryJointType WeightedGlobalNativePairMoments
open scoped BigOperators

theorem ThreeSum.WeightedGlobalNativeMomentBounds.moment_abs_le {N U K k : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (B C : ℕ→ℤ) (i : ℕ) (hk : k≤K)
    (hB : ∀ j<S.left.NL, |B j|≤(U : ℤ)) (hC : ∀ j<S.right.NL, |C j|≤(U : ℤ)) :
    |∑ p : Pair S i, mass S i p*mode B C p^k|≤(momentBound S U K : ℤ) := by sorry
