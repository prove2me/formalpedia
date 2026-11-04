-- Prove2me | Theorems.Thm_ThreeSum_WeightedNearEnumeration_admitted_iff
-- name    : ThreeSum.WeightedNearEnumeration.admitted_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:34:03.949206+00:00
-- url     : https://prove2.me/theorems/d2a838c7-270e-4f42-af89-bd40311ba94c
-- title:
--   Weighted Near Enumeration: admitted iff
-- statement:
--   The Weighted Near Enumeration construction uses the admitted iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearEnumeration.lean#L96-L114
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearEnumeration.lean#L96-L114

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_NearEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearEnumeration
open ThreeSum.WeightedAddresses ThreeSum.WeightedEnumeration

theorem ThreeSum.WeightedNearEnumeration.admitted_iff (qs rs : List ℕ) (D : ℕ) :
    Admitted qs rs D ↔ List.Forall₂ (· ≤ ·) rs qs ∧
      (List.zipWith (fun q r => digitCost q-digitCost r) qs rs).sum ≤ D := by sorry
