-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_gradMat_eq_ccc0be16809b
-- name    : P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_gradMat_eq_ccc0be16809b
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:18:51.938815+00:00
-- url     : https://prove2.me/theorems/c5bc5141-915f-477b-b1fb-9df7caa62f27
-- title:
--   P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt grad Mat eq ccc0be16809b: P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt grad Mat eq ccc0be16809b
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt grad Mat eq ccc0be16809b construction uses the P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt grad Mat eq ccc0be16809b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L127-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L127-L130

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

theorem P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_gradMat_eq_ccc0be16809b {D : ℕ} {v : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (hv : DifferentiableAt ℝ v z) :
    gradMat v v z = vecMulVec (fun j => dz j (cplx v) z) (star fun j => dz j (cplx v) z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartCutoffEnergyAlt».«gradMat_eq» := P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_gradMat_eq_ccc0be16809b
