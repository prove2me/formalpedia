-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_chartCutoff_eq_86e7091cfeb0
-- name    : P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_chartCutoff_eq_86e7091cfeb0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:36.45251+00:00
-- url     : https://prove2.me/theorems/c2fbd7f5-a4ad-4b51-8f16-342a392392a9
-- title:
--   P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt chart Cutoff eq 86e7091cfeb0: P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt chart Cutoff eq 86e7091cfeb0
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt chart Cutoff eq 86e7091cfeb0 construction uses the P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt chart Cutoff eq 86e7091cfeb0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L29-L30

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

theorem P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_chartCutoff_eq_86e7091cfeb0 {D : ℕ} (k : ℕ) (y : Fin D → ℂ) :
    chartCutoff k y = Real.smoothTransition (2 - sqn y / ((k : ℝ) + 1) ^ 2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartCutoffEnergyAlt».«chartCutoff_eq» := P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_chartCutoff_eq_86e7091cfeb0
