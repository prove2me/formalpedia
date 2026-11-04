-- Prove2me | Theorems.Thm_ThreeSum_WeightedNearEnumeration_mem_codes_lt
-- name    : ThreeSum.WeightedNearEnumeration.mem_codes_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:34:10.51205+00:00
-- url     : https://prove2.me/theorems/40e27251-fac1-4d2c-ba4c-9ae1fe74eec7
-- title:
--   Weighted Near Enumeration: mem codes lt
-- statement:
--   The Weighted Near Enumeration construction uses the mem codes lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearEnumeration.lean#L151-L156
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearEnumeration.lean#L151-L156

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_NearEnumeration
import Theorems.Thm_ThreeSum_TernaryAddresses_mem_codes_lt
import Theorems.Thm_ThreeSum_WeightedAddresses_mem_codes_lt

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearEnumeration
open ThreeSum.WeightedAddresses ThreeSum.WeightedEnumeration

theorem ThreeSum.WeightedNearEnumeration.mem_codes_lt {qs : List ℕ} {D a : ℕ}
    (hq : ∀ q ∈ qs, q < 3) (ha : a ∈ codes qs D) : a < 4^qs.length := by sorry
