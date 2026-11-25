-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_finrank_eq_5a18b3f2a1cb
-- name    : P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_finrank_eq_5a18b3f2a1cb
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:17:46.755329+00:00
-- url     : https://prove2.me/theorems/a1f88993-b53e-4079-bf0f-3393d7273cd7
-- title:
--   P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt finrank eq 5a18b3f2a1cb: P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt finrank eq 5a18b3f2a1cb
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt finrank eq 5a18b3f2a1cb construction uses the P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt finrank eq 5a18b3f2a1cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L267-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L267-L270

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

theorem P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_finrank_eq_5a18b3f2a1cb (n : ℕ) : Module.finrank ℝ (Fin (n + 1) → ℂ) = 2 * n + 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartCutoffEnergyAlt».«finrank_eq» := P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_finrank_eq_5a18b3f2a1cb
