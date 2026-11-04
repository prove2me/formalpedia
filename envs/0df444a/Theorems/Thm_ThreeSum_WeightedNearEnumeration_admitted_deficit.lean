-- Prove2me | Theorems.Thm_ThreeSum_WeightedNearEnumeration_admitted_deficit
-- name    : ThreeSum.WeightedNearEnumeration.admitted_deficit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:34:01.156807+00:00
-- url     : https://prove2.me/theorems/2cff823a-5635-47d1-8547-a145de755964
-- title:
--   Weighted Near Enumeration: admitted deficit
-- statement:
--   The Weighted Near Enumeration construction uses the admitted deficit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearEnumeration.lean#L82-L94
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearEnumeration.lean#L82-L94

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_NearEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearEnumeration
open ThreeSum.WeightedAddresses ThreeSum.WeightedEnumeration

theorem ThreeSum.WeightedNearEnumeration.admitted_deficit {qs rs : List ℕ} {D : ℕ} (h : Admitted qs rs D) :
    (List.zipWith (fun q r => digitCost q-digitCost r) qs rs).sum ≤ D := by sorry
