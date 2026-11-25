-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_chartInv_zero_9bd5aa8cc784
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_chartInv_zero_9bd5aa8cc784
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:19:13.940794+00:00
-- url     : https://prove2.me/theorems/bd1e8f0d-6369-435d-b11b-acbf7c96a2d8
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian chart Inv zero 9bd5aa8cc784: P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian chart Inv zero 9bd5aa8cc784
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian chart Inv zero 9bd5aa8cc784 construction uses the P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian chart Inv zero 9bd5aa8cc784 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergySwap.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergySwap.lean#L22-L23

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

theorem P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_chartInv_zero_9bd5aa8cc784 (y : Fin (e + 1) → ℂ) : chartInv y 0 = (y 0)⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergySwapHessian».«chartInv_zero» := P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_chartInv_zero_9bd5aa8cc784
