-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativeMomentBounds_mode_abs_le
-- name    : ThreeSum.WeightedGlobalNativeMomentBounds.mode_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:07:01.974166+00:00
-- url     : https://prove2.me/theorems/04f14c1c-a686-4b4b-b507-307a060928bc
-- title:
--   Weighted Global Native Moment Bounds: mode abs le
-- statement:
--   The Weighted Global Native Moment Bounds construction uses the mode abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeMomentBounds.lean#L64-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeMomentBounds.lean#L64-L71

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativeMomentBounds
open Finset TernaryJointType WeightedGlobalNativePairMoments
open scoped BigOperators

theorem ThreeSum.WeightedGlobalNativeMomentBounds.mode_abs_le {N U : ℕ} {S : WeightedSourceCountExecutionFactory.Setup N} {i : ℕ}
    (B C : ℕ→ℤ) (hB : ∀ j<S.left.NL, |B j|≤(U : ℤ))
    (hC : ∀ j<S.right.NL, |C j|≤(U : ℤ)) (p : Pair S i) :
    |mode B C p|≤2*(U : ℤ) := by sorry
