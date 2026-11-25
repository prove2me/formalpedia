-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_hasCompactSupport_chartCutoff_zero_e61a96b7ce17
-- name    : P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_hasCompactSupport_chartCutoff_zero_e61a96b7ce17
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:19:38.965423+00:00
-- url     : https://prove2.me/theorems/653db5bb-8f72-4839-9c2d-c0a30591e33a
-- title:
--   P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt has Compact Support chart Cutoff zero e61a96b7ce17: P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt has Compact Support chart Cu
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt has Compact Support chart Cutoff zero e61a96b7ce17 construction uses the P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt has Compact Support chart Cutoff zero e61a96b7ce17 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L58-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L58-L69

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

theorem P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_hasCompactSupport_chartCutoff_zero_e61a96b7ce17 {D : ℕ} :
    HasCompactSupport (chartCutoff 0 : (Fin D → ℂ) → ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartCutoffEnergyAlt».«hasCompactSupport_chartCutoff_zero» := P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_hasCompactSupport_chartCutoff_zero_e61a96b7ce17
