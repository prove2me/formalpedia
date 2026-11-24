-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_sqn_nonneg_fadf2dd021f1
-- name    : P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_sqn_nonneg_fadf2dd021f1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:36.412285+00:00
-- url     : https://prove2.me/theorems/04144641-5cdf-433e-8a37-d5b5fdf752f1
-- title:
--   P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt sqn nonneg fadf2dd021f1: P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt sqn nonneg fadf2dd021f1
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt sqn nonneg fadf2dd021f1 construction uses the P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt sqn nonneg fadf2dd021f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L19-L20

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

theorem P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_sqn_nonneg_fadf2dd021f1 {D : ℕ} (y : Fin D → ℂ) : 0 ≤ sqn y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartCutoffEnergyAlt».«sqn_nonneg» := P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_sqn_nonneg_fadf2dd021f1
