-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearEnumeration_mem_codes_lt
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearEnumeration.mem_codes_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:13:28.617608+00:00
-- url     : https://prove2.me/theorems/43055630-50c2-4c02-9c59-d5ed2190af1c
-- title:
--   mem_codes_lt
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearEnumeration.lean#L151-L156
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearEnumeration.lean#L151-L156

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Addresses
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearEnumeration
import Theorems.Thm_ThreeSum_TernaryAddresses_mem_codes_lt
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedAddresses_mem_codes_lt

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearEnumeration
open ThreeSum.WeightedAddresses ThreeSum.WeightedEnumeration

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearEnumeration.mem_codes_lt {qs : List ℕ} {D a : ℕ}
    (hq : ∀ q ∈ qs, q < 3) (ha : a ∈ codes qs D) : a < 4^qs.length := by sorry
