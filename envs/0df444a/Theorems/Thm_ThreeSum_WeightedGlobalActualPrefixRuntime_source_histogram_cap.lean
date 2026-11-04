-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualPrefixRuntime_source_histogram_cap
-- name    : ThreeSum.WeightedGlobalActualPrefixRuntime.source_histogram_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:07:43.643238+00:00
-- url     : https://prove2.me/theorems/bb991fb4-d6e9-4f1b-b105-94996c5b15fd
-- title:
--   Weighted Global Actual Prefix Runtime: source histogram cap
-- statement:
--   Actual per-original source join cap in the exact histogram API consumed
--   by SourceHostBudget. It includes all map-labelled duplicate key records.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L57-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L57-L78

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

theorem ThreeSum.WeightedGlobalActualPrefixRuntime.source_histogram_cap {p m F : ℕ} [Fact p.Prime]
    (maps : Fin F→Weight m p) (cap r : ℕ) (right : Bool) (hp : 2<p) (x : ℤ) :
    let xs:=(localRecords maps cap right).map (TernaryCanonicalDictionaries.native right maps)
    LightHistogram.count
      (fun j=>WantedResidueKeys.code (p^r) 0 (LightTernarySourceHost.dictionary xs p r j))
      (WantedResidueKeys.code (p^r) 0 x) (LightTernarySourceHost.size xs r)≤(F*cap)^r := by sorry
