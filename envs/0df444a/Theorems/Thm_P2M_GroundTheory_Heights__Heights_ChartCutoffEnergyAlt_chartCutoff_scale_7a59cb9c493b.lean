-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_chartCutoff_scale_7a59cb9c493b
-- name    : P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_chartCutoff_scale_7a59cb9c493b
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:17:40.392475+00:00
-- url     : https://prove2.me/theorems/f526c3fd-cfe1-4609-8c88-7ae3a459291e
-- title:
--   P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt chart Cutoff scale 7a59cb9c493b: P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt chart Cutoff scale 7a59cb9c493b
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt chart Cutoff scale 7a59cb9c493b construction uses the P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt chart Cutoff scale 7a59cb9c493b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L36-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L36-L41

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

theorem P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_chartCutoff_scale_7a59cb9c493b {D : ℕ} (k : ℕ) :
    (chartCutoff k : (Fin D → ℂ) → ℝ) = fun y => chartCutoff 0 (((k : ℝ) + 1)⁻¹ • y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartCutoffEnergyAlt».«chartCutoff_scale» := P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_chartCutoff_scale_7a59cb9c493b
