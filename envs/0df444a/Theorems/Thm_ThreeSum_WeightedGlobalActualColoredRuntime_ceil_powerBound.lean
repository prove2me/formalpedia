-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualColoredRuntime_ceil_powerBound
-- name    : ThreeSum.WeightedGlobalActualColoredRuntime.ceil_powerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:47:58.251118+00:00
-- url     : https://prove2.me/theorems/da942eed-31cf-47d1-9212-dfce3f6a6c48
-- title:
--   Weighted Global Actual Colored Runtime: ceil power Bound
-- statement:
--   The Weighted Global Actual Colored Runtime construction uses the ceil power Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualColoredRuntime.lean#L36-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualColoredRuntime.lean#L36-L51

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

theorem ThreeSum.WeightedGlobalActualColoredRuntime.ceil_powerBound {f : ℕ→ℝ} {a : ℝ} (ha : 0≤a) (hf : ∀n,0≤f n)
    (h : ∀ε:ℝ,0<ε→∀ᶠ n:ℕ in atTop,f n≤(n:ℝ)^(a+ε)) :
    PowerBound (fun n=>⌈f n⌉₊) a:= by sorry
