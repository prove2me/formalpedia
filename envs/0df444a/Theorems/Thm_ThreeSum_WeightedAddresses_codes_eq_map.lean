-- Prove2me | Theorems.Thm_ThreeSum_WeightedAddresses_codes_eq_map
-- name    : ThreeSum.WeightedAddresses.codes_eq_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:26:53.624559+00:00
-- url     : https://prove2.me/theorems/e8893aae-86a4-4f5e-9dee-f5b7ed29281c
-- title:
--   Weighted Addresses: codes eq map
-- statement:
--   The Weighted Addresses construction uses the codes eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Addresses.lean#L51-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Addresses.lean#L51-L63

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_Weighted_Enumeration
import Definitions.Def_Submission_Weighted_Addresses
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_eq_map

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedAddresses
open ThreeSum.WeightedEnumeration

theorem ThreeSum.WeightedAddresses.codes_eq_map (n t : ℕ) : codes n t = (words n t).map code := by sorry
