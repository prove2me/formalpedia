-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualPrefixRuntime_source_time_shape
-- name    : ThreeSum.WeightedGlobalActualPrefixRuntime.source_time_shape
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:08:02.031423+00:00
-- url     : https://prove2.me/theorems/b705c8a8-6531-4d05-88d0-1e1dc8712444
-- title:
--   Weighted Global Actual Prefix Runtime: source time shape
-- statement:
--   Bound for the literal SourceHost time function, including all three
--   product dictionaries and the bucket setup even when it emits few matches.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L88-L113
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L88-L113

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

theorem ThreeSum.WeightedGlobalActualPrefixRuntime.source_time_shape (xs ys zs : List ℤ) (hxy : ys.length=xs.length)
    (hxz : zs.length=xs.length) (hm : 1≤xs.length)
    (p J M NL U L bank groups cap : ℕ) (input : ℕ→ℤ)
    (hcap : ∀i<NL, LightHistogram.count
      (fun j=>WantedResidueKeys.code M 0 (LightTernarySourceHost.dictionary xs p J j))
      (WantedResidueKeys.code M 0 (input i)) (LightTernarySourceHost.size xs J)≤cap) :
    LightTernarySourceHost.time xs ys zs p J M NL U L bank groups input≤
      8000*sourceWidth J L U M*sourceVolume xs J M NL bank groups cap := by sorry
