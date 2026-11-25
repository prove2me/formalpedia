-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_gradDens_chartCutoff_left_3d92657897c4
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_gradDens_chartCutoff_left_3d92657897c4
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:29:19.216395+00:00
-- url     : https://prove2.me/theorems/ecc0750f-a036-4b86-89b1-205ee0d3211a
-- title:
--   P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry grad Dens chart Cutoff left 3d92657897c4: P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry grad Dens char
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry grad Dens chart Cutoff left 3d92657897c4 construction uses the P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry grad Dens chart Cutoff left 3d92657897c4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L146-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L146-L149

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyCocycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartCutoffParts
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix MeasureTheory Filter Topology
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartIntegrationByPartsSymmetry
variable {D : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_gradDens_chartCutoff_left_3d92657897c4 {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (w : (Fin (n + 1) → ℂ) → ℝ)
    {k : ℕ} {y : Fin (n + 1) → ℂ} (h : ∑ i, ‖y i‖ ^ 2 < ((k : ℝ) + 1) ^ 2) :
    gradDens φ (chartCutoff k) w y = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntegrationByPartsSymmetry».«gradDens_chartCutoff_left» := P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_gradDens_chartCutoff_left_3d92657897c4
