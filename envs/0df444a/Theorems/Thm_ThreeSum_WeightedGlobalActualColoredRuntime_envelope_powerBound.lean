-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualColoredRuntime_envelope_powerBound
-- name    : ThreeSum.WeightedGlobalActualColoredRuntime.envelope_powerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:46:43.30461+00:00
-- url     : https://prove2.me/theorems/175adc7b-4043-4a5d-a34d-1e5822ffb7c7
-- title:
--   Weighted Global Actual Colored Runtime: envelope power Bound
-- statement:
--   The Weighted Global Actual Colored Runtime construction uses the envelope power Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualColoredRuntime.lean#L53-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualColoredRuntime.lean#L53-L83

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualRuntimeParameters
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparationProof
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramBudget
import Definitions.Def_Submission_Weighted_Global_TernaryActualCleanupRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
import Theorems.Thm_ThreeSum_LightBandRawAResources_envelope_powerBound
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_envelope_powerBound
import Theorems.Thm_ThreeSum_ThreeSumParameterResources_envelope_powerBound
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPairMass_envelope_powerBound

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

theorem ThreeSum.WeightedGlobalActualColoredRuntime.envelope_powerBound {m β κ : ℕ} {δ : ℝ} (hm : 0<m) (hβ : 1<β)
    (hδ : 0≤δ) (hcarry : WeightedGlobalSignedPadding.carryExponent m β (κ:ℝ)<δ)
    (C : ℝ) (hC : 0≤C) (degree : ℕ) :
    PowerBound (envelope C degree m β κ) (WeightedGlobalCountFrontendBudget.frontendExponent+δ):= by sorry
