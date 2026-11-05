-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedAddresses_digitCode_strict
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedAddresses.digitCode_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:06:48.195391+00:00
-- url     : https://prove2.me/theorems/ca4887ae-2b45-4d83-b3a3-c7a1f3d9c754
-- title:
--   digitCode_strict
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Addresses.lean#L37-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Addresses.lean#L37-L39

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Enumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Addresses
import Theorems.Thm_ThreeSum_TernaryAddresses_digitCode_strict

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedAddresses
open ThreeSum.WeightedEnumeration

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedAddresses.digitCode_strict {d e : ℕ} (hd : d < 3) (he : e < 3) (hde : d < e) :
    digitCode d < digitCode e := by sorry
