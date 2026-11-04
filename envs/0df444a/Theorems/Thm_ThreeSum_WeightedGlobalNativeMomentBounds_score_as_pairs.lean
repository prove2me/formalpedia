-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativeMomentBounds_score_as_pairs
-- name    : ThreeSum.WeightedGlobalNativeMomentBounds.score_as_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:12:44.314703+00:00
-- url     : https://prove2.me/theorems/56cb2867-d7d3-448c-92fc-3e195515e42f
-- title:
--   Weighted Global Native Moment Bounds: score as pairs
-- statement:
--   The Weighted Global Native Moment Bounds construction uses the score as pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeMomentBounds.lean#L107-L129
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeMomentBounds.lean#L107-L129

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativeMomentBounds
open Finset TernaryJointType WeightedGlobalNativePairMoments
open scoped BigOperators

theorem ThreeSum.WeightedGlobalNativeMomentBounds.score_as_pairs {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (B C : ℕ→ℤ) (k j i : ℕ) :
    LightWeightedGlobalMomentChannelFactory.score S B C k j i=
      ∑ p : Pair S i, mass S i p*
        LightWeightedGlobalMomentChannelFactory.leftWeights k j B p.val.1.1*
        LightWeightedGlobalMomentChannelFactory.rightWeights k j C p.val.2.1 := by sorry
