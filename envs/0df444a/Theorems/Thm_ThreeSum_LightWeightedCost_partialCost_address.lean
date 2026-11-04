-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedCost_partialCost_address
-- name    : ThreeSum.LightWeightedCost.partialCost_address
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:49:56.793635+00:00
-- url     : https://prove2.me/theorems/edac6e0e-4398-4f8c-b88c-204c3b557d5d
-- title:
--   Light Weighted Cost: partial Cost address
-- statement:
--   The Light Weighted Cost construction uses the partial Cost address property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightCost.lean#L39-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightCost.lean#L39-L45

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

theorem ThreeSum.LightWeightedCost.partialCost_address {N : ℕ} (w : TritWord N) : partialCost N (address w) N=WeightedBankEnumeration.cacheCost w := by sorry
