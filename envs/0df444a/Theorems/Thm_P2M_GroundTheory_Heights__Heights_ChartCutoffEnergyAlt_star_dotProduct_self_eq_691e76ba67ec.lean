-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_star_dotProduct_self_eq_691e76ba67ec
-- name    : P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_star_dotProduct_self_eq_691e76ba67ec
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:18:42.287144+00:00
-- url     : https://prove2.me/theorems/de12d5c5-941a-4598-ae3f-09a38cff31b1
-- title:
--   P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt star dot Product self eq 691e76ba67ec: P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt star dot Product self eq 691e76ba67ec
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt star dot Product self eq 691e76ba67ec construction uses the P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt star dot Product self eq 691e76ba67ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L185-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L185-L189

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
open ReciprocityTheory.AnForm.A

theorem P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_star_dotProduct_self_eq_691e76ba67ec {D : ℕ} (x : Fin D → ℂ) : star x ⬝ᵥ x = ((sqn x : ℝ) : ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartCutoffEnergyAlt».«star_dotProduct_self_eq» := P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_star_dotProduct_self_eq_691e76ba67ec
