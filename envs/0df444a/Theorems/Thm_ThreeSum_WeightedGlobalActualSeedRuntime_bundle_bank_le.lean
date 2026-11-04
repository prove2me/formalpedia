-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualSeedRuntime_bundle_bank_le
-- name    : ThreeSum.WeightedGlobalActualSeedRuntime.bundle_bank_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:20:40.137353+00:00
-- url     : https://prove2.me/theorems/b2a735e3-91bd-4190-a7c1-f30be18eebaa
-- title:
--   Weighted Global Actual Seed Runtime: bundle bank le
-- statement:
--   The Weighted Global Actual Seed Runtime construction uses the bundle bank le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualSeedRuntime.lean#L381-L390
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualSeedRuntime.lean#L381-L390

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaControllerCore
import Definitions.Def_Submission_Weighted_Global_TernarySeedCoefficientBudget
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixInit
import Definitions.Def_Submission_Weighted_Global_TernaryActualSeedRuntime
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalActualSeedRuntime
open Real Light Filter
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalNativeCompleteFrontend
open WeightedGlobalActualPrefixRuntime WeightedGlobalEntropyRates WeightedGlobalOversizePrime
open WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable

theorem ThreeSum.WeightedGlobalActualSeedRuntime.bundle_bank_le {K k b m n j : ℕ} (hfactor : 1≤nativeFactor K k b m) :
    (WeightedGlobalDimensionBounds.bankSize m j:ℝ)≤volumeBundle K k b m n j:= by sorry
