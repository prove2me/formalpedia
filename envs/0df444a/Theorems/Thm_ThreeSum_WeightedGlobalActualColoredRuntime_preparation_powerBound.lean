-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualColoredRuntime_preparation_powerBound
-- name    : ThreeSum.WeightedGlobalActualColoredRuntime.preparation_powerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:47:33.270298+00:00
-- url     : https://prove2.me/theorems/8cf5e92a-1eb0-49c3-82cb-690aa4e0e41f
-- title:
--   Weighted Global Actual Colored Runtime: preparation power Bound
-- statement:
--   The Weighted Global Actual Colored Runtime construction uses the preparation power Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualColoredRuntime.lean#L164-L181
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualColoredRuntime.lean#L164-L181

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

theorem ThreeSum.WeightedGlobalActualColoredRuntime.preparation_powerBound {m β κ : ℕ} {δ : ℝ} (hm : 0<m) (hβ : 1<β)
    (hδ : 0≤δ) (hcarry : WeightedGlobalSignedPadding.carryExponent m β (κ:ℝ)<δ) :
    PowerBound (fun n=>LightWeightedGlobalColorPreparationProof.time n (J m β κ n) (n^κ)) (1+δ):= by sorry
