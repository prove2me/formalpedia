-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPhysicalPairWordBounds_weighted_as_pairs
-- name    : ThreeSum.WeightedGlobalPhysicalPairWordBounds.weighted_as_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:12:07.741201+00:00
-- url     : https://prove2.me/theorems/8d795401-b70b-40e4-ac0c-a25c8f115fdb
-- title:
--   Weighted Global Physical Pair Word Bounds: weighted as pairs
-- statement:
--   The Weighted Global Physical Pair Word Bounds construction uses the weighted as pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPhysicalPairWordBounds.lean#L24-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPhysicalPairWordBounds.lean#L24-L41

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
import Definitions.Def_Submission_Weighted_Global_TernaryPhysicalPairWordBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPhysicalPairWordBounds
open Finset WeightedGlobalNativePairMoments WeightedGlobalNativeMomentBounds
open scoped BigOperators

theorem ThreeSum.WeightedGlobalPhysicalPairWordBounds.weighted_as_pairs {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (leftWeight rightWeight : ℕ→ℤ) (i : ℕ) :
    weighted S leftWeight rightWeight i=
      ∑ p : Pair S i, mass S i p*leftWeight p.val.1.1*rightWeight p.val.2.1 := by sorry
