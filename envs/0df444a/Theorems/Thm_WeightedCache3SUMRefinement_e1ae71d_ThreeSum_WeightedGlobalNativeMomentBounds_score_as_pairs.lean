-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativeMomentBounds_score_as_pairs
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeMomentBounds.score_as_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:20:23.017703+00:00
-- url     : https://prove2.me/theorems/8aee4fe2-89e0-40b4-a5d9-066c66cbea31
-- title:
--   score_as_pairs
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativeMomentBounds.lean#L107-L129
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativeMomentBounds.lean#L107-L129

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeMomentBounds
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeMomentBounds
open Finset TernaryJointType WeightedGlobalNativePairMoments
open scoped BigOperators

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeMomentBounds.score_as_pairs {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (B C : ℕ→ℤ) (k j i : ℕ) :
    LightWeightedGlobalMomentChannelFactory.score S B C k j i=
      ∑ p : Pair S i, mass S i p*
        LightWeightedGlobalMomentChannelFactory.leftWeights k j B p.val.1.1*
        LightWeightedGlobalMomentChannelFactory.rightWeights k j C p.val.2.1 := by sorry
