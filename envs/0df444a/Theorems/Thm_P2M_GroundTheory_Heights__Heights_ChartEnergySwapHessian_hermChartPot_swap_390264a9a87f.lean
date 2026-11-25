-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_hermChartPot_swap_390264a9a87f
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_hermChartPot_swap_390264a9a87f
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:18:10.68639+00:00
-- url     : https://prove2.me/theorems/170c6ea4-3a55-4311-bb66-36d76b777283
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian herm Chart Pot swap 390264a9a87f: P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian herm Chart Pot swap 390264a9a87f
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian herm Chart Pot swap 390264a9a87f construction uses the P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian herm Chart Pot swap 390264a9a87f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergySwap.lean#L50-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergySwap.lean#L50-L69

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

theorem P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_hermChartPot_swap_390264a9a87f (M : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ) (hM : M.PosDef)
    (y : Fin (e + 1) → ℂ) (hy : y 0 ≠ 0) :
    hermChartPot ((swapFirstTwo e)ᴴ * M * swapFirstTwo e) y = hermChartPot M (chartInv y) + Real.log ‖y 0‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergySwapHessian».«hermChartPot_swap» := P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_hermChartPot_swap_390264a9a87f
