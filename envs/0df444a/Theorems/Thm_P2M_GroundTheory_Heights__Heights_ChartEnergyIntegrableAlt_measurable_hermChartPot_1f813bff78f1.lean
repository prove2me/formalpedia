-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergyIntegrableAlt_measurable_hermChartPot_1f813bff78f1
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergyIntegrableAlt_measurable_hermChartPot_1f813bff78f1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:48.213385+00:00
-- url     : https://prove2.me/theorems/845dd463-0528-48eb-871e-8ab8cb6dfbc1
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Integrable Alt measurable herm Chart Pot 1f813bff78f1: P2 M Ground Theory Heights  Heights Chart Energy Integrable Alt measurable herm Chart Pot 1f813b
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Integrable Alt measurable herm Chart Pot 1f813bff78f1 construction uses the P2 M Ground Theory Heights  Heights Chart Energy Integrable Alt measurable herm Chart Pot 1f813bff78f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyIntegrable.lean#L26-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyIntegrable.lean#L26-L33

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStBA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergyIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyIntegrable
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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory Filter
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartEnergyIntegrableAlt

theorem P2M_GroundTheory_Heights__Heights_ChartEnergyIntegrableAlt_measurable_hermChartPot_1f813bff78f1 {e : ℕ} (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) :
    Measurable (hermChartPot M) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergyIntegrableAlt».«measurable_hermChartPot» := P2M_GroundTheory_Heights__Heights_ChartEnergyIntegrableAlt_measurable_hermChartPot_1f813bff78f1
