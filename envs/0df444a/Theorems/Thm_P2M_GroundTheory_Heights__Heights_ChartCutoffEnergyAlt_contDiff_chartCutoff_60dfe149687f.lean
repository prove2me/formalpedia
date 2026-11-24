-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_contDiff_chartCutoff_60dfe149687f
-- name    : P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_contDiff_chartCutoff_60dfe149687f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:42.509208+00:00
-- url     : https://prove2.me/theorems/2583def3-e197-4a23-bb45-681546df1418
-- title:
--   P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt cont Diff chart Cutoff 60dfe149687f: P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt cont Diff chart Cutoff 60dfe149687f
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt cont Diff chart Cutoff 60dfe149687f construction uses the P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt cont Diff chart Cutoff 60dfe149687f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L43-L47

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

theorem P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_contDiff_chartCutoff_60dfe149687f {D : ℕ} (k : ℕ) : ContDiff ℝ 1 (chartCutoff k : (Fin D → ℂ) → ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartCutoffEnergyAlt».«contDiff_chartCutoff» := P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_contDiff_chartCutoff_60dfe149687f
