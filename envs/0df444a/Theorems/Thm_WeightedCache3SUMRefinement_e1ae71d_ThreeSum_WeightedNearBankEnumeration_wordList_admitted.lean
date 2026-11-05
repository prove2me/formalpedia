-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearBankEnumeration_wordList_admitted
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearBankEnumeration.wordList_admitted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:08:21.955834+00:00
-- url     : https://prove2.me/theorems/4b40436e-33ff-4d82-a58a-8fc0d9ba61da
-- title:
--   wordList_admitted
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearBankEnumeration.lean#L50-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearBankEnumeration.lean#L50-L53

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearBankEnumeration.wordList_admitted {N D : ℕ} (Q R : TritWord N) :
    WeightedNearEnumeration.Admitted (wordList Q) (wordList R) D ↔
      R ∈ nearWords Q D := by sorry
