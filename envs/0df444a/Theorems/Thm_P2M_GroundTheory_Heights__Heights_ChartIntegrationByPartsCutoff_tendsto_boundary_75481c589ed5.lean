-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsCutoff_tendsto_boundary_75481c589ed5
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsCutoff_tendsto_boundary_75481c589ed5
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:27:48.356168+00:00
-- url     : https://prove2.me/theorems/0960121d-7690-495f-8480-0bb98a4eb1c3
-- title:
--   P2 M Ground Theory Heights  Heights Chart Integration By Parts Cutoff tendsto boundary 75481c589ed5: P2 M Ground Theory Heights  Heights Chart Integration By Parts Cutoff tendsto boundary 75481c589ed5
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Integration By Parts Cutoff tendsto boundary 75481c589ed5 construction uses the P2 M Ground Theory Heights  Heights Chart Integration By Parts Cutoff tendsto boundary 75481c589ed5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartIbpCutoff.lean#L60-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartIbpCutoff.lean#L60-L124

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartIbpSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartCutoffParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartIbpCutoff
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

theorem P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsCutoff_tendsto_boundary_75481c589ed5 {T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ} (hT : ∀ i, (T i).PosDef)
    {u w : (Fin (n + 1) → ℂ) → ℝ} {W : ℝ} (hW : ∀ y, ‖w y‖ ≤ W)
    (hE : Integrable (gradDens (fun i => hermChartPot (T i)) u u)) {K : ℝ}
    (hK : ∀ k : ℕ, ∫ y, gradDens (fun i => hermChartPot (T i)) (chartCutoff k) (chartCutoff k) y ≤ K) :
    Tendsto (fun k : ℕ => ∫ y, w y * gradDens (fun i => hermChartPot (T i)) (chartCutoff k) u y) atTop (𝓝 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntegrationByPartsCutoff».«tendsto_boundary» := P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsCutoff_tendsto_boundary_75481c589ed5
