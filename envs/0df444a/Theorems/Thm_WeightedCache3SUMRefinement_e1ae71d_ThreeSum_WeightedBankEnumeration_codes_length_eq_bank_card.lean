-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_codes_length_eq_bank_card
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.codes_length_eq_bank_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:07:29.520679+00:00
-- url     : https://prove2.me/theorems/2a2cb294-1bc5-4fb8-9e2f-222664686bb9
-- title:
--   codes_length_eq_bank_card
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/BankEnumeration.lean#L87-L90
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/BankEnumeration.lean#L87-L90

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.codes_length_eq_bank_card (N T : ℕ) :
    (codes N T).length = (bank N T).card := by sorry
