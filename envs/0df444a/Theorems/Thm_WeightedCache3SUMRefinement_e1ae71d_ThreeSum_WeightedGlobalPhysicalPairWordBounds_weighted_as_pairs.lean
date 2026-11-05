-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPhysicalPairWordBounds_weighted_as_pairs
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPhysicalPairWordBounds.weighted_as_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:30:14.080763+00:00
-- url     : https://prove2.me/theorems/00091faf-8cf9-49ce-9981-a5eeb5caffe4
-- title:
--   weighted_as_pairs
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPhysicalPairWordBounds.lean#L24-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPhysicalPairWordBounds.lean#L24-L41

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPhysicalPairWordBounds.weighted_as_pairs {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (leftWeight rightWeight : ℕ→ℤ) (i : ℕ) :
    weighted S leftWeight rightWeight i=
      ∑ p : Pair S i, mass S i p*leftWeight p.val.1.1*rightWeight p.val.2.1 := by sorry
