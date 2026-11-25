-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_chartInv_chartInv_c2422d3ef73b
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_chartInv_chartInv_c2422d3ef73b
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:18:22.561379+00:00
-- url     : https://prove2.me/theorems/f4627447-5e22-4edf-8da9-50c7c035b11b
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian chart Inv chart Inv c2422d3ef73b: P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian chart Inv chart Inv c2422d3ef73b
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian chart Inv chart Inv c2422d3ef73b construction uses the P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian chart Inv chart Inv c2422d3ef73b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergySwap.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergySwap.lean#L25-L31

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

theorem P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_chartInv_chartInv_c2422d3ef73b {y : Fin (e + 1) → ℂ} (hy : y 0 ≠ 0) : chartInv (chartInv y) = y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergySwapHessian».«chartInv_chartInv» := P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_chartInv_chartInv_c2422d3ef73b
