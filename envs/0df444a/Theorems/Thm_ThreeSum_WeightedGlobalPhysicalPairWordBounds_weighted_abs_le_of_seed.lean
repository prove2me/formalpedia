-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPhysicalPairWordBounds_weighted_abs_le_of_seed
-- name    : ThreeSum.WeightedGlobalPhysicalPairWordBounds.weighted_abs_le_of_seed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:12:09.737142+00:00
-- url     : https://prove2.me/theorems/b2eabd2a-fee3-4ca2-b7f6-aa932c570a32
-- title:
--   Weighted Global Physical Pair Word Bounds: weighted abs le of seed
-- statement:
--   The Weighted Global Physical Pair Word Bounds construction uses the weighted abs le of seed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPhysicalPairWordBounds.lean#L72-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPhysicalPairWordBounds.lean#L72-L77

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
import Definitions.Def_Submission_Weighted_Global_TernaryPhysicalPairWordBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPhysicalPairWordBounds
open Finset WeightedGlobalNativePairMoments WeightedGlobalNativeMomentBounds
open scoped BigOperators

theorem ThreeSum.WeightedGlobalPhysicalPairWordBounds.weighted_abs_le_of_seed {N d boundary : ℕ} {lim : Light.Limits}
    (S : WeightedSourceCountExecutionFactory.Setup N) (μ : ℕ→ℤ)
    (leftWeight rightWeight : ℕ→ℤ) (i : ℕ)
    (H : WeightedSourceCountExecutionFactory.Seed S lim d boundary μ leftWeight rightWeight) :
    |weighted S leftWeight rightWeight i|≤(scoreBound S : ℤ) := by sorry
