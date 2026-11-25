-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_norm_dz_le_fef259233242
-- name    : P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_norm_dz_le_fef259233242
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:18:57.058816+00:00
-- url     : https://prove2.me/theorems/22caf3ed-86be-4405-8195-d7d7dab29838
-- title:
--   P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt norm dz le fef259233242: P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt norm dz le fef259233242
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt norm dz le fef259233242 construction uses the P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt norm dz le fef259233242 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L108-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L108-L125

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

theorem P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_norm_dz_le_fef259233242 {D : ℕ} {v : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (hv : DifferentiableAt ℝ v z)
    (j : Fin D) : ‖dz j (cplx v) z‖ ≤ ‖fderiv ℝ v z‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartCutoffEnergyAlt».«norm_dz_le» := P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_norm_dz_le_fef259233242
