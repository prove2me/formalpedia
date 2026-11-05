-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_wordList_fromList
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.wordList_fromList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:07:29.936822+00:00
-- url     : https://prove2.me/theorems/371e04ed-4bd4-4ff7-801a-7b5da98864e2
-- title:
--   wordList_fromList
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/BankEnumeration.lean#L58-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/BankEnumeration.lean#L58-L63

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Addresses
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration
open ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.TernaryJointType

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.wordList_fromList {N : ℕ} (xs : List ℕ) (hlen : xs.length = N)
    (hdigits : ∀ d ∈ xs, d < 3) : wordList (fromList xs hlen hdigits) = xs := by sorry
