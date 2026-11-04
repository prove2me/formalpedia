-- Prove2me | Theorems.Thm_ThreeSum_WeightedAddresses_codes_nodup
-- name    : ThreeSum.WeightedAddresses.codes_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:30:07.355817+00:00
-- url     : https://prove2.me/theorems/e676e829-8877-4d0f-a2f1-eab570891e98
-- title:
--   Weighted Addresses: codes nodup
-- statement:
--   The Weighted Addresses construction uses the codes nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Addresses.lean#L96-L97
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Addresses.lean#L96-L97

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_Weighted_Enumeration
import Definitions.Def_Submission_Weighted_Addresses
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_nodup

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedAddresses
open ThreeSum.WeightedEnumeration

theorem ThreeSum.WeightedAddresses.codes_nodup (n t : ℕ) : (codes n t).Nodup := by sorry
