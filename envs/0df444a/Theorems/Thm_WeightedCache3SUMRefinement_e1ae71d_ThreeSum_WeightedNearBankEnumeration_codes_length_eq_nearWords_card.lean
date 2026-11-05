-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearBankEnumeration_codes_length_eq_nearWords_card
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearBankEnumeration.codes_length_eq_nearWords_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:08:19.335201+00:00
-- url     : https://prove2.me/theorems/725dd31f-8111-46c8-922f-b3b4b29dcfce
-- title:
--   codes_length_eq_nearWords_card
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearBankEnumeration.lean#L75-L80
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearBankEnumeration.lean#L75-L80

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
import Mathlib.Data.List.Forall2
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearBankEnumeration
open ThreeSum.TernaryJointType ThreeSum.WeightedBankEnumeration
open WeightedCache (Below)
open ThreeSum.WeightedEnumeration (digitCost)

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearBankEnumeration.codes_length_eq_nearWords_card {N : ℕ} (Q : TritWord N) (D : ℕ) :
    (WeightedNearEnumeration.codes (wordList Q) D).length = (nearWords Q D).card := by sorry
