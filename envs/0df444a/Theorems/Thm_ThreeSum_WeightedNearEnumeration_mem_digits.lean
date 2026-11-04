-- Prove2me | Theorems.Thm_ThreeSum_WeightedNearEnumeration_mem_digits
-- name    : ThreeSum.WeightedNearEnumeration.mem_digits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:33:54.054838+00:00
-- url     : https://prove2.me/theorems/be661276-1cd4-4391-886f-42ab02a9545c
-- title:
--   Weighted Near Enumeration: mem digits
-- statement:
--   The Weighted Near Enumeration construction uses the mem digits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearEnumeration.lean#L23-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearEnumeration.lean#L23-L25

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_NearEnumeration
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.WeightedEnumeration.mem_digits


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearEnumeration
open ThreeSum.WeightedAddresses ThreeSum.WeightedEnumeration

theorem ThreeSum.WeightedNearEnumeration.mem_digits {q D r : ℕ} :
    r ∈ digits q D ↔ r ≤ q ∧ digitCost q-digitCost r ≤ D := by sorry
