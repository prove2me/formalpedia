-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergyIntegrableAlt_quad_pos_39af722e88fa
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergyIntegrableAlt_quad_pos_39af722e88fa
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:19:01.103634+00:00
-- url     : https://prove2.me/theorems/10ffe9e6-afcf-4c1b-b8ed-b88b9219a415
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Integrable Alt quad pos 39af722e88fa: P2 M Ground Theory Heights  Heights Chart Energy Integrable Alt quad pos 39af722e88fa
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Integrable Alt quad pos 39af722e88fa construction uses the P2 M Ground Theory Heights  Heights Chart Energy Integrable Alt quad pos 39af722e88fa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyIntegrable.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyIntegrable.lean#L19-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStBA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergyIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyIntegrable
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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory Filter
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartEnergyIntegrableAlt

theorem P2M_GroundTheory_Heights__Heights_ChartEnergyIntegrableAlt_quad_pos_39af722e88fa {e : ℕ} {M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hM : M.PosDef) (y : Fin e → ℂ) :
    0 < (star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ (M *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ))).re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergyIntegrableAlt».«quad_pos» := P2M_GroundTheory_Heights__Heights_ChartEnergyIntegrableAlt_quad_pos_39af722e88fa
