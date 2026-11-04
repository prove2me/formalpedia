-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualPrefixRuntime_wanted_entries_cap
-- name    : ThreeSum.WeightedGlobalActualPrefixRuntime.wanted_entries_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:04:38.461167+00:00
-- url     : https://prove2.me/theorems/d5f37cf7-73a4-4ce3-900b-20bd49bfb63f
-- title:
--   Weighted Global Actual Prefix Runtime: wanted entries cap
-- statement:
--   Literal output rows are counted by the executed wanted DFS, including
--   all repeated map occurrence labels.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L503-L510
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L503-L510

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernarySourceHostBudget
import Definitions.Def_Submission_ThreeSum_TernaryWantedDictionaryFiber
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_Submission_Weighted_Global_TernaryMomentReporterBudget
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedControllerBudget
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScoreFactory
import Definitions.Def_Submission_Weighted_Global_TernarySignedPreparationBudget
import Definitions.Def_Submission_Weighted_Global_TernaryExtensionBudget
import Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalActualPrefixRuntime
open Light Real Filter Asymptotics
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend
open WeightedGlobalEntropyRates WeightedGlobalDimensionBounds WeightedGlobalOversizePrime
open WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale
open scoped BigOperators Topology
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable

theorem ThreeSum.WeightedGlobalActualPrefixRuntime.wanted_entries_cap {p m F j : ℕ} [Fact p.Prime]
    (maps : Fin F→Weight m p) (τ : ℕ) (I : Input) :
    (entries (r:=j) maps τ I).length≤I.requesterCount*(F*WeightedGlobalGoodOutputCatalog.cap m p τ)^j := by sorry
