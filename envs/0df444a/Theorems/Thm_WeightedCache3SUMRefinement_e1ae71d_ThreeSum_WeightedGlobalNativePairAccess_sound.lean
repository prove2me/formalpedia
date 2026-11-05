-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativePairAccess_sound
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePairAccess.sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:26:59.603759+00:00
-- url     : https://prove2.me/theorems/cb31b1f6-0703-48b8-93fc-aa8524ceef84
-- title:
--   sound
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativePairAccess.lean#L28-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativePairAccess.lean#L28-L38

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCanonicalNativeCompleteness
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCompactPairedSupport
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativePairAccess
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePairAccess
open Finset TernaryJointType WeightedGlobalNativePairMoments TernarySourceHostModel
set_option maxHeartbeats 2000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePairAccess.sound {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (A B C : ℕ→ℤ) (position : ℕ→ℕ) (nA : ℕ)
    (hpos : ∀ i<S.front.count, position i<nA) :
    (∃ i<S.front.count, ∃ p : Pair S i, mode B C p=A (position i)) →
    ∃ i<nA, ∃ j<S.left.NL, ∃ k<S.right.NL, C k=A i+B j := by sorry
