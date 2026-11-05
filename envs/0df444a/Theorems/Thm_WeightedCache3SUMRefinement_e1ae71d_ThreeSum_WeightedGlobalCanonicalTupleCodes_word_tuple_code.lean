-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCanonicalTupleCodes_word_tuple_code
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCanonicalTupleCodes.word_tuple_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:39:45.462604+00:00
-- url     : https://prove2.me/theorems/b99aeba8-bc2c-4e57-9ed1-5804fc03f8e7
-- title:
--   word_tuple_code
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryCanonicalTupleCodes.lean#L16-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryCanonicalTupleCodes.lean#L16-L26

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTupleWantedLookup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCanonicalTupleCodes
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCanonicalTupleCodes
open TernaryJointType
set_option maxHeartbeats 2000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCanonicalTupleCodes.word_tuple_code {A : Type*} {L : ℕ} (word : A→TritWord L) (xs : List A) :
    Radix.positionalHash ((4^L : ℕ) : ℤ)
      (fun a => (TernaryCodeSemantics.address (word a) : ℤ)) xs=
      (TernaryAddresses.code (xs.reverse.flatMap (TernaryBankEnumeration.wordList ∘ word)) : ℤ) := by sorry
