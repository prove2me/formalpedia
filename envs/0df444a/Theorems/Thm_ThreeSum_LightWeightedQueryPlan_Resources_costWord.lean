-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedQueryPlan_Resources_costWord
-- name    : ThreeSum.LightWeightedQueryPlan.Resources.costWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:25:44.249731+00:00
-- url     : https://prove2.me/theorems/0d411220-415f-470b-b07e-88e8aa5c36ba
-- title:
--   Resources: cost Word
-- statement:
--   The Resources construction uses the cost Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/QueryPlan.lean#L70-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/QueryPlan.lean#L70-L75

import Definitions.Def_Submission_Weighted_WantedQuery
import Definitions.Def_Submission_Weighted_NearSetup
import Definitions.Def_Submission_Weighted_QueryPlan
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedQueryPlan
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryEuler ThreeSum.TernaryCodeSemantics ThreeSum.LightWeightedNearPair

theorem ThreeSum.LightWeightedQueryPlan.Resources.costWord {lim : Limits} {N rows : ℕ} {c : Config}
    {source : TritWord N→ℤ} (R : Resources lim rows c source) :
    ((1025*N+1100 : ℕ) : ℤ)≤lim.word := by sorry
