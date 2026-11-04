-- Prove2me | Theorems.Thm_ThreeSum_WeightedAddresses_mem_codes_lt
-- name    : ThreeSum.WeightedAddresses.mem_codes_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:28:27.649069+00:00
-- url     : https://prove2.me/theorems/11f4a48a-8809-488a-b822-1e669430cc5e
-- title:
--   Weighted Addresses: mem codes lt
-- statement:
--   The Weighted Addresses construction uses the mem codes lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Addresses.lean#L68-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Addresses.lean#L68-L72

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_Weighted_Enumeration
import Definitions.Def_Submission_Weighted_Addresses
import Theorems.Thm_ThreeSum_TernaryAddresses_mem_codes_lt

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedAddresses
open ThreeSum.WeightedEnumeration

theorem ThreeSum.WeightedAddresses.mem_codes_lt {n t a : ℕ} (ha : a ∈ codes n t) : a < 4 ^ n := by sorry
