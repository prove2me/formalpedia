-- Prove2me | Theorems.Thm_P2M_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearEnumeration_admitted_forall__b67294c6681c
-- name    : P2M_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearEnumeration_admitted_forall__b67294c6681c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:07:38.977394+00:00
-- url     : https://prove2.me/theorems/a416f8e7-14fa-4974-a86f-6d6f7dba77c6
-- title:
--   P2M_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearEnumeration_admitted_forall__b67294c6681c
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearEnumeration.lean#L73-L80
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearEnumeration.lean#L73-L80

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Addresses
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearEnumeration
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearEnumeration
open ThreeSum.WeightedAddresses ThreeSum.WeightedEnumeration

theorem P2M_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearEnumeration_admitted_forall__b67294c6681c {qs rs : List ℕ} {D : ℕ} (h : Admitted qs rs D) :
    List.Forall₂ (· ≤ ·) rs qs := by sorry

alias «WeightedCache3SUMRefinement_e1ae71d».«ThreeSum».«WeightedNearEnumeration».«admitted_forall₂» := P2M_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearEnumeration_admitted_forall__b67294c6681c
