-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualSeedRuntime_span_time_shape
-- name    : ThreeSum.WeightedGlobalActualSeedRuntime.span_time_shape
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:23:19.40298+00:00
-- url     : https://prove2.me/theorems/f5cacd42-1d12-4608-8725-464067b37784
-- title:
--   Weighted Global Actual Seed Runtime: span time shape
-- statement:
--   The Weighted Global Actual Seed Runtime construction uses the span time shape property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualSeedRuntime.lean#L375-L379
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualSeedRuntime.lean#L375-L379

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaControllerCore
import Definitions.Def_Submission_Weighted_Global_TernarySeedCoefficientBudget
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixInit
import Definitions.Def_Submission_Weighted_Global_TernaryActualSeedRuntime
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows


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

theorem ThreeSum.WeightedGlobalActualSeedRuntime.span_time_shape (J p rows : ℕ) :
    LightSpanCatalogStep.time J p rows≤spanCoefficient p*(J+1)*(rows+1):= by sorry
