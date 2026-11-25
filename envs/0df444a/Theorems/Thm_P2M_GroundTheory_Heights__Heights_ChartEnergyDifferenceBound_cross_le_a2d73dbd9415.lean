-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergyDifferenceBound_cross_le_a2d73dbd9415
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergyDifferenceBound_cross_le_a2d73dbd9415
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:23:32.205206+00:00
-- url     : https://prove2.me/theorems/84273a14-9e4e-4673-9825-7ef0852d41b1
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Difference Bound cross le a2d73dbd9415: P2 M Ground Theory Heights  Heights Chart Energy Difference Bound cross le a2d73dbd9415
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Difference Bound cross le a2d73dbd9415 construction uses the P2 M Ground Theory Heights  Heights Chart Energy Difference Bound cross le a2d73dbd9415 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartDiffEnergy.lean#L17-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartDiffEnergy.lean#L17-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartIbpSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartCutoffParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDiffEnergy
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
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartEnergyDifferenceBound

theorem P2M_GroundTheory_Heights__Heights_ChartEnergyDifferenceBound_cross_le_a2d73dbd9415 {u U χ a p G : ℝ} (hU : |u| ≤ U) (hχ : 0 ≤ χ) (hp : 0 ≤ p) (hG : 0 ≤ G)
    (ha : |a| ≤ Real.sqrt p * Real.sqrt G) :
    -(u * (χ * a + χ * a)) ≤ 2 * U ^ 2 * p + χ * χ * G / 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergyDifferenceBound».«cross_le» := P2M_GroundTheory_Heights__Heights_ChartEnergyDifferenceBound_cross_le_a2d73dbd9415
