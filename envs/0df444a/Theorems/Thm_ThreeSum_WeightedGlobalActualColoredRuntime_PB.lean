-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualColoredRuntime_PB
-- name    : ThreeSum.WeightedGlobalActualColoredRuntime.PB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:47:12.151097+00:00
-- url     : https://prove2.me/theorems/1e93a694-4262-4c22-998c-b05b1f8d17a8
-- title:
--   Weighted Global Actual Colored Runtime: PB
-- statement:
--   The whole size-only per-color envelope has exponent strictly below
--   the final1.921 target, before the outer subpolynomial coloring scan.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualColoredRuntime.lean#L405-L420
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualColoredRuntime.lean#L405-L420

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

theorem ThreeSum.WeightedGlobalActualColoredRuntime.PB {K k c d m F D E κ B H β : ℕ} {δ : ℝ}
    (hm : 0<m) (hβ : 1<β) (hδ : 0≤δ)
    (hcarry : WeightedGlobalSignedPadding.carryExponent m β (κ:ℝ)<δ)
    (hroom : WeightedGlobalCountFrontendBudget.frontendExponent+δ≤exponent) :
    PowerBound (uniformTime K k c d m F D E κ B H β) exponent:= by sorry
