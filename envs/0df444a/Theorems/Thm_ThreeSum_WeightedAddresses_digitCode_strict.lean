-- Prove2me | Theorems.Thm_ThreeSum_WeightedAddresses_digitCode_strict
-- name    : ThreeSum.WeightedAddresses.digitCode_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:25:49.035778+00:00
-- url     : https://prove2.me/theorems/2089f45c-8e86-44e7-910b-1c41042957f3
-- title:
--   Weighted Addresses: digit Code strict
-- statement:
--   The Weighted Addresses construction uses the digit Code strict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Addresses.lean#L37-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Addresses.lean#L37-L39

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_Weighted_Enumeration
import Definitions.Def_Submission_Weighted_Addresses
import Theorems.Thm_ThreeSum_TernaryAddresses_digitCode_strict

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedAddresses
open ThreeSum.WeightedEnumeration

theorem ThreeSum.WeightedAddresses.digitCode_strict {d e : ℕ} (hd : d < 3) (he : e < 3) (hde : d < e) :
    digitCode d < digitCode e := by sorry
