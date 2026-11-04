-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalGlobalPreludeResources_need_bound
-- name    : ThreeSum.WeightedGlobalGlobalPreludeResources.need_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:10:48.051773+00:00
-- url     : https://prove2.me/theorems/5e3ceff2-939e-4f28-bfa6-bb5f0880174f
-- title:
--   Weighted Global Global Prelude Resources: need bound
-- statement:
--   The Weighted Global Global Prelude Resources construction uses the need bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGlobalPreludeResources.lean#L94-L111
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGlobalPreludeResources.lean#L94-L111

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryGlobalPreludeProof
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensionsBudget
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_Weighted_Global_TernaryGlobalPreludeResources
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalGlobalPreludeResources
open Light LightWeightedGlobalGlobalPrelude
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalGlobalPreludeResources.need_bound {M b p K : ℕ} [Fact p.Prime] (hM : 1<M) (hb : 1<b) (κ n U : ℕ) :
    (need M b p K κ n U).word≤coefficient M b p K κ*(n+1)^(exponent κ) ∧
    (need M b p K κ n U).cells≤coefficient M b p K κ*(n+1)^(exponent κ) ∧
    (need M b p K κ n U).depth≤coefficient M b p K κ*(n+1)^(exponent κ) := by sorry
