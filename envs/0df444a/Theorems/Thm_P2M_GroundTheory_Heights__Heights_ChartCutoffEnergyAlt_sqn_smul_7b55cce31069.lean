-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_sqn_smul_7b55cce31069
-- name    : P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_sqn_smul_7b55cce31069
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:19.386573+00:00
-- url     : https://prove2.me/theorems/31c5e7ee-ea27-4ab1-b966-e75c957bf264
-- title:
--   P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt sqn smul 7b55cce31069: P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt sqn smul 7b55cce31069
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt sqn smul 7b55cce31069 construction uses the P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt sqn smul 7b55cce31069 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L22-L23

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

theorem P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_sqn_smul_7b55cce31069 {D : ℕ} (c : ℝ) (y : Fin D → ℂ) : sqn (c • y) = c ^ 2 * sqn y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartCutoffEnergyAlt».«sqn_smul» := P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_sqn_smul_7b55cce31069
