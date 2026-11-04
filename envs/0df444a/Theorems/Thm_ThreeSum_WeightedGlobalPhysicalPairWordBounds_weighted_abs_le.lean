-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPhysicalPairWordBounds_weighted_abs_le
-- name    : ThreeSum.WeightedGlobalPhysicalPairWordBounds.weighted_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:12:33.169211+00:00
-- url     : https://prove2.me/theorems/06b54565-7a30-4537-aa94-5047a6cbe4db
-- title:
--   Weighted Global Physical Pair Word Bounds: weighted abs le
-- statement:
--   The Weighted Global Physical Pair Word Bounds construction uses the weighted abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPhysicalPairWordBounds.lean#L43-L70
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPhysicalPairWordBounds.lean#L43-L70

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
import Definitions.Def_Submission_Weighted_Global_TernaryPhysicalPairWordBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPhysicalPairWordBounds
open Finset WeightedGlobalNativePairMoments WeightedGlobalNativeMomentBounds
open scoped BigOperators

theorem ThreeSum.WeightedGlobalPhysicalPairWordBounds.weighted_abs_le {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (leftWeight rightWeight : ℕ→ℤ) (i : ℕ)
    (hL : ∀ a<S.left.NL, |leftWeight a|≤(S.left.weightU : ℤ))
    (hR : ∀ a<S.right.NL, |rightWeight a|≤(S.right.weightU : ℤ)) :
    |weighted S leftWeight rightWeight i|≤(scoreBound S : ℤ) := by sorry
