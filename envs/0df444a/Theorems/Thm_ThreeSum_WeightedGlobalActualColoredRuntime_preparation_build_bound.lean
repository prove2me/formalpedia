-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualColoredRuntime_preparation_build_bound
-- name    : ThreeSum.WeightedGlobalActualColoredRuntime.preparation_build_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:46:48.827706+00:00
-- url     : https://prove2.me/theorems/db78f605-27cd-4426-9d43-35bc9a3fe982
-- title:
--   Weighted Global Actual Colored Runtime: preparation build bound
-- statement:
--   The Weighted Global Actual Colored Runtime construction uses the preparation build bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualColoredRuntime.lean#L85-L134
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualColoredRuntime.lean#L85-L134

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualRuntimeParameters
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparationProof
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramBudget
import Definitions.Def_Submission_Weighted_Global_TernaryActualCleanupRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalActualColoredRuntime
open Light Real Filter StageBounds ArithmeticStageBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalNativeCompleteFrontend
open WeightedGlobalActualPrefixRuntime WeightedGlobalActualSeedRuntime WeightedGlobalEntropyRates
open WeightedGlobalOversizePrime WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale
open scoped Topology BigOperators
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable

theorem ThreeSum.WeightedGlobalActualColoredRuntime.preparation_build_bound {n : ℕ} (hn : 1≤n) (J U : ℕ) :
    LightWeightedGlobalColorPreparationProof.buildTime n n n J U≤
      100000*n*2^J*(J+1)^2*(Nat.log 2 (3*U+1)+2)^2:= by sorry
