-- Prove2me | Theorems.Thm_P2M_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearBankEnumeration_wordList_forall__e9c823a4b5ec
-- name    : P2M_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearBankEnumeration_wordList_forall__e9c823a4b5ec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:08:36.459866+00:00
-- url     : https://prove2.me/theorems/c74f5a09-8723-4154-9615-d2b91be7515e
-- title:
--   P2M_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearBankEnumeration_wordList_forall__e9c823a4b5ec
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearBankEnumeration.lean#L24-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearBankEnumeration.lean#L24-L37

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

theorem P2M_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearBankEnumeration_wordList_forall__e9c823a4b5ec {N : ℕ} (R Q : TritWord N) :
    List.Forall₂ (· ≤ ·) (wordList R) (wordList Q) ↔ Below R Q := by sorry

alias «WeightedCache3SUMRefinement_e1ae71d».«ThreeSum».«WeightedNearBankEnumeration».«wordList_forall₂» := P2M_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearBankEnumeration_wordList_forall__e9c823a4b5ec
