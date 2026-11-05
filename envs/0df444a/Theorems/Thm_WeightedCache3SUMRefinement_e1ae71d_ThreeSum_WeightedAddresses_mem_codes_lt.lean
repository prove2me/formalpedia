-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedAddresses_mem_codes_lt
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedAddresses.mem_codes_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:06:59.847938+00:00
-- url     : https://prove2.me/theorems/5f8c050c-2ef2-4882-96ad-59427ac9d5fd
-- title:
--   mem_codes_lt
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Addresses.lean#L68-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Addresses.lean#L68-L72

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Enumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Addresses
import Theorems.Thm_ThreeSum_TernaryAddresses_mem_codes_lt

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedAddresses
open ThreeSum.WeightedEnumeration

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedAddresses.mem_codes_lt {n t a : ℕ} (ha : a ∈ codes n t) : a < 4 ^ n := by sorry
