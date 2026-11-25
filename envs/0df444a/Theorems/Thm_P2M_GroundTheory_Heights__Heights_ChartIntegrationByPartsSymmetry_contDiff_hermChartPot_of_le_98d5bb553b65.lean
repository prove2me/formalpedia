-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_contDiff_hermChartPot_of_le_98d5bb553b65
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_contDiff_hermChartPot_of_le_98d5bb553b65
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:37:07.954012+00:00
-- url     : https://prove2.me/theorems/3e2f4872-0ee2-4f1f-9325-d948415a2016
-- title:
--   P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry cont Diff herm Chart Pot of le 98d5bb553b65: P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry cont Diff h
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry cont Diff herm Chart Pot of le 98d5bb553b65 construction uses the P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry cont Diff herm Chart Pot of le 98d5bb553b65 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L28-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L28-L33

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
variable {e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_contDiff_hermChartPot_of_le_98d5bb553b65 (m : ℕ) {M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hM : M.PosDef) :
    ContDiff ℝ m (hermChartPot M) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntegrationByPartsSymmetry».«contDiff_hermChartPot_of_le» := P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_contDiff_hermChartPot_of_le_98d5bb553b65
