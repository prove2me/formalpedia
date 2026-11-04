-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedCost_partialCost_succ
-- name    : ThreeSum.LightWeightedCost.partialCost_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:21:31.153987+00:00
-- url     : https://prove2.me/theorems/ae26dc58-10b0-4b70-918f-9896559aa060
-- title:
--   Light Weighted Cost: partial Cost succ
-- statement:
--   The Light Weighted Cost construction uses the partial Cost succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightCost.lean#L24-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightCost.lean#L24-L25

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_Weighted_LightCost
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedCost
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
open ThreeSum.WeightedEnumeration
open Light Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.LightSubsetAddress

theorem ThreeSum.LightWeightedCost.partialCost_succ (N m j : ℕ) :
    partialCost N m (j+1)=partialCost N m j+digitCost (digitAt N m j) := by sorry
