-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualGlobalQueryRuntime_queryCap_le
-- name    : ThreeSum.WeightedGlobalActualGlobalQueryRuntime.queryCap_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T00:09:27.694772+00:00
-- url     : https://prove2.me/theorems/7f1210af-7a09-446a-ade4-8f71b442a163
-- title:
--   Weighted Global Actual Global Query Runtime: query Cap le
-- statement:
--   The Weighted Global Actual Global Query Runtime construction uses the query Cap le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualGlobalQueryRuntime.lean#L55-L59
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualGlobalQueryRuntime.lean#L55-L59

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryUniformQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryActualGlobalQueryRuntime
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalActualGlobalQueryRuntime
open Light Real Filter StageBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalNativeCompleteFrontend
open WeightedGlobalActualPrefixRuntime WeightedGlobalActualSeedRuntime WeightedGlobalActualColoredRuntime
open WeightedGlobalOversizePrime WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale WeightedGlobalEntropyRates
open scoped Topology BigOperators
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable

theorem ThreeSum.WeightedGlobalActualGlobalQueryRuntime.queryCap_le {K m n q : ℕ} (S : State K m)
    (hphase : ∀j≤radixLength m n,(S.phase j).queryTime≤q) (hpost : S.post.queryTime≤q) :
    queryCap S n≤q:= by sorry
