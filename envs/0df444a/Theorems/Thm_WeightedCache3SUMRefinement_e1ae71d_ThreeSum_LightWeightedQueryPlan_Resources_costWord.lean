-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedQueryPlan_Resources_costWord
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedQueryPlan.Resources.costWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:49:05.484204+00:00
-- url     : https://prove2.me/theorems/caee0ac3-dcca-45ba-a6eb-a1232a477af5
-- title:
--   costWord
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/QueryPlan.lean#L70-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/QueryPlan.lean#L70-L75

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_WantedQuery
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_QueryPlan
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedQueryPlan
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryEuler ThreeSum.TernaryCodeSemantics ThreeSum.LightWeightedNearPair

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedQueryPlan.Resources.costWord {lim : Limits} {N rows : ℕ} {c : Config}
    {source : TritWord N→ℤ} (R : Resources lim rows c source) :
    ((2740*N+3000 : ℕ) : ℤ)≤lim.word := by sorry
