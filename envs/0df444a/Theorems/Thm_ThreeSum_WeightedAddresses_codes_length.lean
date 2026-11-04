-- Prove2me | Theorems.Thm_ThreeSum_WeightedAddresses_codes_length
-- name    : ThreeSum.WeightedAddresses.codes_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:27:29.006533+00:00
-- url     : https://prove2.me/theorems/638df8b0-8d41-433c-847a-0e497e4b99dd
-- title:
--   Weighted Addresses: codes length
-- statement:
--   The Weighted Addresses construction uses the codes length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Addresses.lean#L65-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Addresses.lean#L65-L66

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_Weighted_Enumeration
import Definitions.Def_Submission_Weighted_Addresses
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
attribute [local simp] ThreeSum.TernaryAddresses.codes_length


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedAddresses
open ThreeSum.WeightedEnumeration

theorem ThreeSum.WeightedAddresses.codes_length (n t : ℕ) : (codes n t).length = (words n t).length := by sorry
