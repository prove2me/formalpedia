-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_norm_fderiv_chartCutoff_le_69838da594e8
-- name    : P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_norm_fderiv_chartCutoff_le_69838da594e8
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:18:41.180795+00:00
-- url     : https://prove2.me/theorems/351e5d50-30d1-41b9-8029-26f5a24ab213
-- title:
--   P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt norm fderiv chart Cutoff le 69838da594e8: P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt norm fderiv chart Cutoff le 69838da594
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt norm fderiv chart Cutoff le 69838da594e8 construction uses the P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt norm fderiv chart Cutoff le 69838da594e8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L71-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L71-L89

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

theorem P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_norm_fderiv_chartCutoff_le_69838da594e8 {D : ℕ} (k : ℕ) (y : Fin D → ℂ) :
    ‖fderiv ℝ (chartCutoff k : (Fin D → ℂ) → ℝ) y‖ ≤
      ((k : ℝ) + 1)⁻¹ * ‖fderiv ℝ (chartCutoff 0 : (Fin D → ℂ) → ℝ) (((k : ℝ) + 1)⁻¹ • y)‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartCutoffEnergyAlt».«norm_fderiv_chartCutoff_le» := P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_norm_fderiv_chartCutoff_le_69838da594e8
