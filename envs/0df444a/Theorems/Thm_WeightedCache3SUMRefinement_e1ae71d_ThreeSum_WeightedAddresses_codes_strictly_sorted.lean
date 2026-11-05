-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedAddresses_codes_strictly_sorted
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedAddresses.codes_strictly_sorted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:06:42.994694+00:00
-- url     : https://prove2.me/theorems/b4da3820-bcb0-43bb-8585-edbfbd012eb6
-- title:
--   codes_strictly_sorted
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Addresses.lean#L74-L94
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Addresses.lean#L74-L94

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Enumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Addresses
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_strictly_sorted

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedAddresses
open ThreeSum.WeightedEnumeration

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedAddresses.codes_strictly_sorted (n t : ℕ) : (codes n t).Pairwise (· < ·) := by sorry
