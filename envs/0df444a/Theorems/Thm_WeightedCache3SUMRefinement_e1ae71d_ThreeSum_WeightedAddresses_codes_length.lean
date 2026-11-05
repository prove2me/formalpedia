-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedAddresses_codes_length
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedAddresses.codes_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:06:33.071191+00:00
-- url     : https://prove2.me/theorems/9407ded3-fcd8-48c3-9536-24099551a13d
-- title:
--   codes_length
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Addresses.lean#L65-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Addresses.lean#L65-L66

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Enumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Addresses
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
attribute [local simp] ThreeSum.TernaryAddresses.codes_length


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedAddresses
open ThreeSum.WeightedEnumeration

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedAddresses.codes_length (n t : ℕ) : (codes n t).length = (words n t).length := by sorry
