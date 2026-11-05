-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalActualColoredRuntime_envelope_powerBound
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualColoredRuntime.envelope_powerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:55:30.543647+00:00
-- url     : https://prove2.me/theorems/5be26091-2adb-40d4-9020-3c9c3383439f
-- title:
--   envelope_powerBound
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryActualColoredRuntime.lean#L53-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryActualColoredRuntime.lean#L53-L83

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualRuntimeParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColorPreparationProof
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryFastProgramBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualCleanupRuntime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualColoredRuntime
import Theorems.Thm_ThreeSum_LightBandRawAResources_envelope_powerBound
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_envelope_powerBound
import Theorems.Thm_ThreeSum_ThreeSumParameterResources_envelope_powerBound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPairMass_envelope_powerBound

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualColoredRuntime
open Light Real Filter StageBounds ArithmeticStageBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalNativeCompleteFrontend
open WeightedGlobalActualPrefixRuntime WeightedGlobalActualSeedRuntime WeightedGlobalEntropyRates
open WeightedGlobalOversizePrime WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale
open scoped Topology BigOperators
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualColoredRuntime.envelope_powerBound {m β κ : ℕ} {δ : ℝ} (hm : 0<m) (hβ : 1<β)
    (hδ : 0≤δ) (hcarry : WeightedGlobalSignedPadding.carryExponent m β (κ:ℝ)<δ)
    (C : ℝ) (hC : 0≤C) (degree : ℕ) :
    PowerBound (envelope C degree m β κ) (WeightedGlobalCountFrontendBudget.frontendExponent+δ):= by sorry
