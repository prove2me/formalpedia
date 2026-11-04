-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalGlobalPreludeResources_need_poly
-- name    : ThreeSum.WeightedGlobalGlobalPreludeResources.need_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:03:33.012192+00:00
-- url     : https://prove2.me/theorems/68229a06-b7a0-4b96-8f60-118114e84b36
-- title:
--   Weighted Global Global Prelude Resources: need poly
-- statement:
--   The Weighted Global Global Prelude Resources construction uses the need poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGlobalPreludeResources.lean#L113-L123
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGlobalPreludeResources.lean#L113-L123

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

theorem ThreeSum.WeightedGlobalGlobalPreludeResources.need_poly {M b p K : ℕ} [Fact p.Prime] (hM : 1<M) (hb : 1<b) (κ : ℕ) :
    PolyNeed (need M b p K κ) := by sorry
