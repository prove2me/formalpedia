-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearEnumeration_admitted_iff
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearEnumeration.admitted_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:07:42.831319+00:00
-- url     : https://prove2.me/theorems/fc31c5ef-bbe2-4a3f-a399-d23ed48aca66
-- title:
--   admitted_iff
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearEnumeration.lean#L96-L114
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearEnumeration.lean#L96-L114

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Addresses
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearEnumeration
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearEnumeration
open ThreeSum.WeightedAddresses ThreeSum.WeightedEnumeration

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearEnumeration.admitted_iff (qs rs : List ℕ) (D : ℕ) :
    Admitted qs rs D ↔ List.Forall₂ (· ≤ ·) rs qs ∧
      (List.zipWith (fun q r => digitCost q-digitCost r) qs rs).sum ≤ D := by sorry
