-- Prove2me | Theorems.Thm_ThreeSum_WeightedBankCanonical_sorted
-- name    : ThreeSum.WeightedBankCanonical.sorted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:58:07.299781+00:00
-- url     : https://prove2.me/theorems/6906f3bf-c13c-4dfd-b79c-6d04e36f3e84
-- title:
--   Weighted Bank Canonical: sorted
-- statement:
--   The Weighted Bank Canonical construction uses the sorted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankCanonical.lean#L51-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankCanonical.lean#L51-L56

import Definitions.Def_Submission_Weighted_BankStageModel
import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_BankCanonical
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedBankCanonical
open ThreeSum.TernaryJointType ThreeSum.WeightedEnumeration
open ThreeSum.WeightedAddresses ThreeSum.WeightedBankEnumeration ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedBankCanonical.sorted (N T : ℕ) : ∀ j k, j<k → k<(codes N T).length →
    address ((enumeration N T).word j)<address ((enumeration N T).word k) := by sorry
