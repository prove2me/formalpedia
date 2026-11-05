-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalRepeatedWords_adds
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalRepeatedWords.adds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:29:44.123476+00:00
-- url     : https://prove2.me/theorems/224dc4b1-13ad-467d-9687-4c0550c58855
-- title:
--   adds
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryRepeatedWords.lean#L37-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryRepeatedWords.lean#L37-L40

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryWantedFactorial
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeCoverWitness
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryRepeatedWords
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalRepeatedWords
open TernaryJointType Finset
open scoped BigOperators
set_option maxHeartbeats 3000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalRepeatedWords.adds {r L : ℕ} (a b q : Fin r → TritWord L)
    (h : ∀ i, PointwiseSum (a i) (b i) (q i)) : PointwiseSum (word a) (word b) (word q) := by sorry
