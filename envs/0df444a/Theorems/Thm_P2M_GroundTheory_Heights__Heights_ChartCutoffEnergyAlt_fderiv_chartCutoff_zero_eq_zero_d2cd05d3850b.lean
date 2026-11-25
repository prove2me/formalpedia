-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_fderiv_chartCutoff_zero_eq_zero_d2cd05d3850b
-- name    : P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_fderiv_chartCutoff_zero_eq_zero_d2cd05d3850b
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:17:21.835473+00:00
-- url     : https://prove2.me/theorems/367c083d-c8be-40e8-b992-074c178d75a7
-- title:
--   P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt fderiv chart Cutoff zero eq zero d2cd05d3850b: P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt fderiv chart Cutoff zero eq zero
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt fderiv chart Cutoff zero eq zero d2cd05d3850b construction uses the P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt fderiv chart Cutoff zero eq zero d2cd05d3850b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L49-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L49-L56

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartCutoffEnergy
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm Matrix MeasureTheory Filter
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartCutoffEnergyAlt

theorem P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_fderiv_chartCutoff_zero_eq_zero_d2cd05d3850b {D : ℕ} {x : Fin D → ℂ} (hx : sqn x < 1) :
    fderiv ℝ (chartCutoff 0 : (Fin D → ℂ) → ℝ) x = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartCutoffEnergyAlt».«fderiv_chartCutoff_zero_eq_zero» := P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_fderiv_chartCutoff_zero_eq_zero_d2cd05d3850b
