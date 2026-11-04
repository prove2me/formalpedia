-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedWantedQuery_assembled_product_eq
-- name    : ThreeSum.LightWeightedWantedQuery.assembled_product_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:21:12.545605+00:00
-- url     : https://prove2.me/theorems/12b2000a-a30b-42f3-81d9-84fa2fbd0fc9
-- title:
--   Light Weighted Wanted Query: assembled product eq
-- statement:
--   The assembler's product is the full transformed product consumed by both
--   near reconstruction and the frozen query.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/WantedQuery.lean#L135-L138
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/WantedQuery.lean#L135-L138

import Definitions.Def_Submission_Weighted_NearPair
import Definitions.Def_Submission_Weighted_FrozenPhysical
import Definitions.Def_Submission_Weighted_BankAssembly
import Definitions.Def_Submission_Weighted_WantedQuery
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedWantedQuery
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.WeightedBankStageModel
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.LightWeightedNearPair
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedWantedQuery.assembled_product_eq {N : ℕ} (F G : TritWord N→ℤ) :
    LightWeightedBankAssembly.product F G=H F G := by sorry
