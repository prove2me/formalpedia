-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualGlobalQueryRuntime_wanted_count_le_cap
-- name    : ThreeSum.WeightedGlobalActualGlobalQueryRuntime.wanted_count_le_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T00:00:59.363808+00:00
-- url     : https://prove2.me/theorems/63b61f9e-0807-4b03-8a3c-20997b501a7e
-- title:
--   Weighted Global Actual Global Query Runtime: wanted count le cap
-- statement:
--   The Weighted Global Actual Global Query Runtime construction uses the wanted count le cap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualGlobalQueryRuntime.lean#L106-L114
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualGlobalQueryRuntime.lean#L106-L114

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

theorem ThreeSum.WeightedGlobalActualGlobalQueryRuntime.wanted_count_le_cap {K k m F n digitLength j : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (I : Input)
    (hF : 0<F) (hj : j≤radixLength m n) (hrequest : I.requesterCount≤n*2^digitLength) :
    (entries (r:=j) maps (threshold K k m) I).length≤wantedCap K k m F n digitLength:= by sorry
