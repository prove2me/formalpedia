-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_hessC_eq_cxHessian_ae8a5d56a517
-- name    : P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_hessC_eq_cxHessian_ae8a5d56a517
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:18:47.874318+00:00
-- url     : https://prove2.me/theorems/16f8d0bc-ffe6-4165-81c2-cc560f34749a
-- title:
--   P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt hess C eq cx Hessian ae8a5d56a517: P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt hess C eq cx Hessian ae8a5d56a517
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt hess C eq cx Hessian ae8a5d56a517 construction uses the P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt hess C eq cx Hessian ae8a5d56a517 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L183-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L183-L183

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

theorem P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_hessC_eq_cxHessian_ae8a5d56a517 {D : ℕ} (φ : (Fin D → ℂ) → ℝ) : hessC φ = cxHessian φ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartCutoffEnergyAlt».«hessC_eq_cxHessian» := P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_hessC_eq_cxHessian_ae8a5d56a517
