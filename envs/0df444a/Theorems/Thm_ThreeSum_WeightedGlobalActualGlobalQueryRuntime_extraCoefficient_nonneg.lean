-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualGlobalQueryRuntime_extraCoefficient_nonneg
-- name    : ThreeSum.WeightedGlobalActualGlobalQueryRuntime.extraCoefficient_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T00:01:04.88493+00:00
-- url     : https://prove2.me/theorems/df68b640-0273-41e7-a99e-837e9c0d2843
-- title:
--   Weighted Global Actual Global Query Runtime: extra Coefficient nonneg
-- statement:
--   The Weighted Global Actual Global Query Runtime construction uses the extra Coefficient nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualGlobalQueryRuntime.lean#L315-L318
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualGlobalQueryRuntime.lean#L315-L318

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

theorem ThreeSum.WeightedGlobalActualGlobalQueryRuntime.extraCoefficient_nonneg (K k c d m F D E κ B H : ℕ) :
    0≤extraCoefficient K k c d m F D E κ B H:= by sorry
