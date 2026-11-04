-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualColoredRuntime_prelude_time_bound
-- name    : ThreeSum.WeightedGlobalActualColoredRuntime.prelude_time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:42:18.546577+00:00
-- url     : https://prove2.me/theorems/d0099e00-3f80-4a35-9adc-4d7528b4e8d0
-- title:
--   Weighted Global Actual Colored Runtime: prelude time bound
-- statement:
--   The Weighted Global Actual Colored Runtime construction uses the prelude time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualColoredRuntime.lean#L136-L152
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualColoredRuntime.lean#L136-L152

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

theorem ThreeSum.WeightedGlobalActualColoredRuntime.prelude_time_bound {n : ℕ} (hn : 1<n) :
    LightTernaryColorPrelude.time n≤20000*(n+1)*(LightColorParametersCosts.width n+1):= by sorry
