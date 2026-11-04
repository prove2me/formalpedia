-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPhysicalPairWordBounds_weighted_abs_le_caps
-- name    : ThreeSum.WeightedGlobalPhysicalPairWordBounds.weighted_abs_le_caps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:12:11.246758+00:00
-- url     : https://prove2.me/theorems/9752af91-e7a1-458d-bce5-92c37b0e02a2
-- title:
--   Weighted Global Physical Pair Word Bounds: weighted abs le caps
-- statement:
--   Independent numeric caps allow the final caller to choose uniform
--   source-weight bounds before constructing the per-channel source setups.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPhysicalPairWordBounds.lean#L81-L106
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPhysicalPairWordBounds.lean#L81-L106

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
import Definitions.Def_Submission_Weighted_Global_TernaryPhysicalPairWordBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPhysicalPairWordBounds
open Finset WeightedGlobalNativePairMoments WeightedGlobalNativeMomentBounds
open scoped BigOperators

theorem ThreeSum.WeightedGlobalPhysicalPairWordBounds.weighted_abs_le_caps {N U V : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (leftWeight rightWeight : ℕ→ℤ) (i : ℕ)
    (hL : ∀ a<S.left.NL, |leftWeight a|≤(U : ℤ))
    (hR : ∀ a<S.right.NL, |rightWeight a|≤(V : ℤ)) :
    |weighted S leftWeight rightWeight i|≤(pairBound S*2^N*U*V : ℕ) := by sorry
