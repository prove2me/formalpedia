-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedAddresses_code_lt
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedAddresses.code_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:06:43.820763+00:00
-- url     : https://prove2.me/theorems/8a36928e-e138-48e5-8214-5f67a6fd2610
-- title:
--   code_lt
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Addresses.lean#L41-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Addresses.lean#L41-L49

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Enumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Addresses
import Theorems.Thm_ThreeSum_TernaryAddresses_code_lt

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedAddresses
open ThreeSum.WeightedEnumeration

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedAddresses.code_lt (xs : List ℕ) (h : ∀ d ∈ xs, d < 3) : code xs < 4 ^ xs.length := by sorry
