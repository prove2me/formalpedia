-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativeMomentBounds_indices_lt
-- name    : ThreeSum.WeightedGlobalNativeMomentBounds.indices_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:06:24.865805+00:00
-- url     : https://prove2.me/theorems/12ab56d4-12b9-46ae-8fa3-593950f6779d
-- title:
--   Weighted Global Native Moment Bounds: indices lt
-- statement:
--   The Weighted Global Native Moment Bounds construction uses the indices lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeMomentBounds.lean#L41-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeMomentBounds.lean#L41-L50

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativeMomentBounds
open Finset TernaryJointType WeightedGlobalNativePairMoments
open scoped BigOperators

theorem ThreeSum.WeightedGlobalNativeMomentBounds.indices_lt {N : ℕ} {S : WeightedSourceCountExecutionFactory.Setup N} {i : ℕ}
    (p : Pair S i) : p.val.1.1<S.left.NL ∧ p.val.2.1<S.right.NL := by sorry
