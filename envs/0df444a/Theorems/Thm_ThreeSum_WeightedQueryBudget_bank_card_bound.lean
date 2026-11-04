-- Prove2me | Theorems.Thm_ThreeSum_WeightedQueryBudget_bank_card_bound
-- name    : ThreeSum.WeightedQueryBudget.bank_card_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:45:58.265419+00:00
-- url     : https://prove2.me/theorems/bea2251d-f4e1-46a2-bc58-ce3ab33c0aae
-- title:
--   Weighted Query Budget: bank card bound
-- statement:
--   The Weighted Query Budget construction uses the bank card bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/QueryBudget.lean#L58-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/QueryBudget.lean#L58-L71

import Definitions.Def_Submission_Weighted_PreparedWanted
import Definitions.Def_Submission_Weighted_Schedule
import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_Weighted_QueryBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedQueryBudget
open Real TernaryJointType WeightedSchedule WeightedCacheParameters
open WeightedBankEnumeration (cacheCost)
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedQueryBudget.bank_card_bound (m : ℕ) :
    ((WeightedAddresses.codes (fixedLength m) (bankCut m)).length : ℝ)≤
      exp ((fixedLength m : ℝ)*Bn) := by sorry
