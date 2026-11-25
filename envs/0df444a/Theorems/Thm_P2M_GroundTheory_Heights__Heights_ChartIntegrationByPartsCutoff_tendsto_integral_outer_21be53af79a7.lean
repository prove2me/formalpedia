-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsCutoff_tendsto_integral_outer_21be53af79a7
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsCutoff_tendsto_integral_outer_21be53af79a7
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:28:25.342405+00:00
-- url     : https://prove2.me/theorems/bf00ebb6-1f3e-4d7b-855e-98fe4c2934f8
-- title:
--   P2 M Ground Theory Heights  Heights Chart Integration By Parts Cutoff tendsto integral outer 21be53af79a7: P2 M Ground Theory Heights  Heights Chart Integration By Parts Cutoff tendsto integral outer
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Integration By Parts Cutoff tendsto integral outer 21be53af79a7 construction uses the P2 M Ground Theory Heights  Heights Chart Integration By Parts Cutoff tendsto integral outer 21be53af79a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartIbpCutoff.lean#L41-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartIbpCutoff.lean#L41-L58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartIbpSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartCutoffParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartIbpCutoff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_IsConeSetB_indicator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix MeasureTheory Filter Topology
open ChartIntegrationByPartsSymmetry
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartIntegrationByPartsCutoff
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsCutoff_tendsto_integral_outer_21be53af79a7 {g : (Fin (n + 1) → ℂ) → ℝ} (hg : Integrable g) :
    Tendsto (fun k : ℕ => ∫ y, (outer n k).indicator g y) atTop (𝓝 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntegrationByPartsCutoff».«tendsto_integral_outer» := P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsCutoff_tendsto_integral_outer_21be53af79a7
