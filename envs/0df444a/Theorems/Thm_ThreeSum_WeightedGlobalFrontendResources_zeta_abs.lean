-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_zeta_abs
-- name    : ThreeSum.WeightedGlobalFrontendResources.zeta_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:27:22.442549+00:00
-- url     : https://prove2.me/theorems/aff46a7a-b881-4464-a41b-3222b01267bf
-- title:
--   Weighted Global Frontend Resources: zeta abs
-- statement:
--   The Weighted Global Frontend Resources construction uses the zeta abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/FrontendResources.lean#L101-L106
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/FrontendResources.lean#L101-L106

import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_Weighted_Global_TernaryRadixOverhead
import Definitions.Def_Submission_Weighted_Global_FrontendResources
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalFrontendResources
open Light ThreeSum.TernaryJointType ThreeSum.WeightedGlobalBank ThreeSum.TernaryEuler
open ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedQueryPlan
open ThreeSum.WeightedBankStageModel ThreeSum.LightWeightedPreparedWanted
open Filter StageBounds ThreeSum.TernaryCodeSemantics
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000

theorem ThreeSum.WeightedGlobalFrontendResources.zeta_abs {N A : ℕ} (F : TritWord N→ ℤ)
    (hF : ∀ R, |F R|≤ (A:ℤ)) (R : TritWord N) :
    |binomialZeta F R|≤ (sourceZeta N A:ℤ) := by sorry
