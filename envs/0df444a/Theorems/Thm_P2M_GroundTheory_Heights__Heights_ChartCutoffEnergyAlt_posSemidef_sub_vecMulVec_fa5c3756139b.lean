-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_posSemidef_sub_vecMulVec_fa5c3756139b
-- name    : P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_posSemidef_sub_vecMulVec_fa5c3756139b
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:19:32.921243+00:00
-- url     : https://prove2.me/theorems/d9ab2f6c-d74a-4e07-9ce9-a7980f02f99e
-- title:
--   P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt pos Semidef sub vec Mul Vec fa5c3756139b: P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt pos Semidef sub vec Mul Vec fa5c375613
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt pos Semidef sub vec Mul Vec fa5c3756139b construction uses the P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt pos Semidef sub vec Mul Vec fa5c3756139b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L132-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L132-L161

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

theorem P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_posSemidef_sub_vecMulVec_fa5c3756139b {D : ℕ} (a : Fin D → ℂ) :
    (((∑ j, ‖a j‖ ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) - vecMulVec a (star a)).PosSemidef := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartCutoffEnergyAlt».«posSemidef_sub_vecMulVec» := P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_posSemidef_sub_vecMulVec_fa5c3756139b
