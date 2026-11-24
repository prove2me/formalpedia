-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_contDiff_sqn_38acd465955c
-- name    : P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_contDiff_sqn_38acd465955c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:03.323514+00:00
-- url     : https://prove2.me/theorems/5abd4dc3-f960-4e9b-a662-0324512a2988
-- title:
--   P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt cont Diff sqn 38acd465955c: P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt cont Diff sqn 38acd465955c
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt cont Diff sqn 38acd465955c construction uses the P2 M Ground Theory Heights  Heights Chart Cutoff Energy Alt cont Diff sqn 38acd465955c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean#L25-L27

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

theorem P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_contDiff_sqn_38acd465955c {D : ℕ} : ContDiff ℝ 1 (sqn (D := D)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartCutoffEnergyAlt».«contDiff_sqn» := P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_contDiff_sqn_38acd465955c
