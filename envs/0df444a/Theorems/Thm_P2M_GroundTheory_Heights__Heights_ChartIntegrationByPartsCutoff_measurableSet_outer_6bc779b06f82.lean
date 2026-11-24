-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsCutoff_measurableSet_outer_6bc779b06f82
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsCutoff_measurableSet_outer_6bc779b06f82
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:22.935851+00:00
-- url     : https://prove2.me/theorems/338c5989-f050-4c8d-a923-324f8deced50
-- title:
--   P2 M Ground Theory Heights  Heights Chart Integration By Parts Cutoff measurable Set outer 6bc779b06f82: P2 M Ground Theory Heights  Heights Chart Integration By Parts Cutoff measurable Set outer 6bc7
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Integration By Parts Cutoff measurable Set outer 6bc779b06f82 construction uses the P2 M Ground Theory Heights  Heights Chart Integration By Parts Cutoff measurable Set outer 6bc779b06f82 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartIbpCutoff.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartIbpCutoff.lean#L37-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartIbpSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartCutoffParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartIbpCutoff
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix MeasureTheory Filter Topology
open ChartIntegrationByPartsSymmetry
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartIntegrationByPartsCutoff
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsCutoff_measurableSet_outer_6bc779b06f82 (k : ℕ) : MeasurableSet (outer n k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntegrationByPartsCutoff».«measurableSet_outer» := P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsCutoff_measurableSet_outer_6bc779b06f82
