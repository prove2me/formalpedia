-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_chartCutoff_zero_eq_1b604a4b9efd
-- name    : P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_chartCutoff_zero_eq_1b604a4b9efd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:39.908809+00:00
-- url     : https://prove2.me/theorems/076f2c03-0d53-4f6f-9f61-044824f76226
-- title:
--   P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt chart Cutoff zero eq 1b604a4b9efd: P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt chart Cutoff zero eq 1b604a4b9efd
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt chart Cutoff zero eq 1b604a4b9efd construction uses the P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt chart Cutoff zero eq 1b604a4b9efd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L32-L34

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

theorem P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_chartCutoff_zero_eq_1b604a4b9efd {D : ℕ} (y : Fin D → ℂ) :
    chartCutoff 0 y = Real.smoothTransition (2 - sqn y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartCutoffEnergyAlt».«chartCutoff_zero_eq» := P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_chartCutoff_zero_eq_1b604a4b9efd
