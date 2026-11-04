-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualPrefixRuntime_canonical_source_time
-- name    : ThreeSum.WeightedGlobalActualPrefixRuntime.canonical_source_time
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:04:47.218605+00:00
-- url     : https://prove2.me/theorems/e69dff02-13e3-40bd-a96e-9bdb893eebb4
-- title:
--   Weighted Global Actual Prefix Runtime: canonical source time
-- statement:
--   The exact canonical source setup discharges the histogram cap, rather
--   than asking for a generic bound on its execution.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L117-L129
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L117-L129

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

theorem ThreeSum.WeightedGlobalActualPrefixRuntime.canonical_source_time {p m F r : ℕ} [Fact p.Prime]
    (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (hp : 2<p) (hpos : 1≤(localRecords maps cap right).length) :
    (source (r:=r) maps cap I right).runtime≤
      8000*sourceWidth r (2*N m r) ((source (r:=r) maps cap I right).U) (p^r)*
        sourceVolume ((source (r:=r) maps cap I right).xs) r (p^r)
          (if right then I.nC else I.nB) (nb m r) (F^r) ((F*cap)^r) := by sorry
