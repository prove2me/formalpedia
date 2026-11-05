-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearEnumeration_codes_strictly_sorted
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearEnumeration.codes_strictly_sorted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:14:20.397127+00:00
-- url     : https://prove2.me/theorems/a93b64df-d76f-40d2-969a-ce07d6b39f09
-- title:
--   codes_strictly_sorted
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearEnumeration.lean#L158-L180
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearEnumeration.lean#L158-L180

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Addresses
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearEnumeration
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_strictly_sorted
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedAddresses_codes_strictly_sorted

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearEnumeration
open ThreeSum.WeightedAddresses ThreeSum.WeightedEnumeration

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearEnumeration.codes_strictly_sorted (qs : List ℕ) (D : ℕ) (hq : ∀ q ∈ qs, q < 3) :
    (codes qs D).Pairwise (· < ·) := by sorry
