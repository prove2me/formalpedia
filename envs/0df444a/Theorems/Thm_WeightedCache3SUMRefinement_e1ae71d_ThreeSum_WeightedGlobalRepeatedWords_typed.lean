-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalRepeatedWords_typed
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalRepeatedWords.typed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:29:36.318302+00:00
-- url     : https://prove2.me/theorems/1fc79a3b-5942-469c-90c2-f72d5eeb7f97
-- title:
--   typed
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryRepeatedWords.lean#L25-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryRepeatedWords.lean#L25-L35

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalRepeatedWords.typed {r L : ℕ} (blocks : Fin r → TritWord L) (π : DigitType)
    (h : ∀ i, HasType (blocks i) π) : HasType (word blocks) (fun d => r*π d) := by sorry
