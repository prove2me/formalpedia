-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualGlobalQueryRuntime_PB
-- name    : ThreeSum.WeightedGlobalActualGlobalQueryRuntime.PB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T01:28:56.862859+00:00
-- url     : https://prove2.me/theorems/94d18250-ffd3-4d5c-9319-b672f1ed47f1
-- title:
--   Weighted Global Actual Global Query Runtime: PB
-- statement:
--   The Weighted Global Actual Global Query Runtime construction uses the PB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualGlobalQueryRuntime.lean#L382-L390
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualGlobalQueryRuntime.lean#L382-L390

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryUniformQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryActualGlobalQueryRuntime
import Theorems.Thm_ThreeSum_WeightedGlobalActualColoredRuntime_PB

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

theorem ThreeSum.WeightedGlobalActualGlobalQueryRuntime.PB {K k c d m F D E κ B H β : ℕ} {δ : ℝ}
    (hm : 0<m) (hβ : 1<β) (hδ : 0≤δ)
    (hcarry : WeightedGlobalSignedPadding.carryExponent m β (κ:ℝ)<δ)
    (hroom : WeightedGlobalCountFrontendBudget.frontendExponent+δ≤WeightedGlobalActualColoredRuntime.exponent) :
    PowerBound (uniformTime K k c d m F D E κ B H β) WeightedGlobalActualColoredRuntime.exponent:= by sorry
