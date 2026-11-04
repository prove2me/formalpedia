-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPrefixSeedHeader_result_seg
-- name    : ThreeSum.WeightedGlobalPrefixSeedHeader.result_seg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:05:53.810367+00:00
-- url     : https://prove2.me/theorems/ddca0baf-073a-4c44-b14d-f66263511810
-- title:
--   Weighted Global Prefix Seed Header: result seg
-- statement:
--   The Weighted Global Prefix Seed Header construction uses the result seg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixSeedHeader.lean#L22-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixSeedHeader.lean#L22-L33

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixSeedHeader
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrefixSeedHeader
open Light LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
open LightWeightedGlobalPrefixStep LightWeightedGlobalPrefixHeader LightWeightedGlobalPrefixFinish
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalPrefixSeedHeader.result_seg {μ : ℕ→ℤ} {xs : List ℤ} (X : Inputs) (H : Seg μ X.seed xs) :
    Seg (LightTernaryBudgetStep.changed
      (LightWeightedGlobalPrefixPrepare.seedChanged μ X.seed X.power X.liveHeader (X.j+1))
      (X.seed+41) X.p X.a X.b X.scale X.xB X.xC X.xP X.tB X.tC X.tP)
      X.seed (result xs X) := by sorry
