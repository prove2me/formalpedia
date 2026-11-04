-- Prove2me | Theorems.Thm_ThreeSum_WeightedBankCanonical_address_word
-- name    : ThreeSum.WeightedBankCanonical.address_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:57:45.962953+00:00
-- url     : https://prove2.me/theorems/db907603-d861-4175-9631-e3d87297c0be
-- title:
--   Weighted Bank Canonical: address word
-- statement:
--   The Weighted Bank Canonical construction uses the address word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankCanonical.lean#L43-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankCanonical.lean#L43-L49

import Definitions.Def_Submission_Weighted_BankStageModel
import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_BankCanonical
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedBankCanonical
open ThreeSum.TernaryJointType ThreeSum.WeightedEnumeration
open ThreeSum.WeightedAddresses ThreeSum.WeightedBankEnumeration ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedBankCanonical.address_word {N T j : ℕ} (hj : j<(codes N T).length) :
    address (word N T j)=(codes N T)[j] := by sorry
