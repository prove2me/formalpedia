-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPhysicalPairWordBounds_weighted_abs_le
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPhysicalPairWordBounds.weighted_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:30:52.829302+00:00
-- url     : https://prove2.me/theorems/84d1a193-9abe-4555-99f0-fba17a085949
-- title:
--   weighted_abs_le
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPhysicalPairWordBounds.lean#L43-L70
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPhysicalPairWordBounds.lean#L43-L70

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeMomentBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPhysicalPairWordBounds
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPhysicalPairWordBounds
open Finset WeightedGlobalNativePairMoments WeightedGlobalNativeMomentBounds
open scoped BigOperators

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPhysicalPairWordBounds.weighted_abs_le {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (leftWeight rightWeight : ℕ→ℤ) (i : ℕ)
    (hL : ∀ a<S.left.NL, |leftWeight a|≤(S.left.weightU : ℤ))
    (hR : ∀ a<S.right.NL, |rightWeight a|≤(S.right.weightU : ℤ)) :
    |weighted S leftWeight rightWeight i|≤(scoreBound S : ℤ) := by sorry
