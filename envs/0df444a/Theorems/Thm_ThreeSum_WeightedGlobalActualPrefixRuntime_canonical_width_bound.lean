-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualPrefixRuntime_canonical_width_bound
-- name    : ThreeSum.WeightedGlobalActualPrefixRuntime.canonical_width_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:07:19.670333+00:00
-- url     : https://prove2.me/theorems/8d5be448-2839-4ca4-860a-939bbe11504e
-- title:
--   Weighted Global Actual Prefix Runtime: canonical width bound
-- statement:
--   Tight query width for the actual canonical configs, obtained from the
--   same fixed polynomial word envelope already needed by the executable.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L888-L910
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L888-L910

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

theorem ThreeSum.WeightedGlobalActualPrefixRuntime.canonical_width_bound {p m F n j U κ D E : ℕ} [Fact p.Prime]
    (maps : Fin F→Weight m p) (cap : ℕ) (I : Input)
    (hm : 0<m) (hn : 1<n) (hj : j≤radixLength m n) (hU : U≤n^κ)
    (hV : WeightedGlobalFrontendResources.eulerBound (N m j) (valueCap (r:=j) maps cap I)≤D*(n+U+1)^E) :
    WeightedGlobalCountFrontendBudget.width (N m j)
      (nearConfig (m:=m) (r:=j) I false (valueCap (r:=j) maps cap I))
      (nearConfig (m:=m) (r:=j) I true (valueCap (r:=j) maps cap I))≤
      (5*fixedLength m+2*capacityBits (outputSize m) D E κ+3)*(radixLength m n+1) := by sorry
