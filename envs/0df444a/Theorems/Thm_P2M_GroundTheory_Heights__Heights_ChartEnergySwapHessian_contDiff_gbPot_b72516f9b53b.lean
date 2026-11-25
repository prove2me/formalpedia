-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_contDiff_gbPot_b72516f9b53b
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_contDiff_gbPot_b72516f9b53b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:19:16.414721+00:00
-- url     : https://prove2.me/theorems/5bd16a6b-0924-4f43-bf5b-69c86ab24e27
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian cont Diff gb Pot b72516f9b53b: P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian cont Diff gb Pot b72516f9b53b
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian cont Diff gb Pot b72516f9b53b construction uses the P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian cont Diff gb Pot b72516f9b53b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergySwap.lean#L71-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergySwap.lean#L71-L75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartHessHolo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergySwap
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Matrix MeasureTheory Filter Topology
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartEnergySwapHessian
open ChartMongeAmpereAffineInvariance
variable {e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_contDiff_gbPot_b72516f9b53b {D : ℕ} : ContDiff ℝ 2 (gbPot (D := D)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergySwapHessian».«contDiff_gbPot» := P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_contDiff_gbPot_b72516f9b53b
