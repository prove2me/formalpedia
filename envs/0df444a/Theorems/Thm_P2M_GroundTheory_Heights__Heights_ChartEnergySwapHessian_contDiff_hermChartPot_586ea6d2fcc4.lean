-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_contDiff_hermChartPot_586ea6d2fcc4
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_contDiff_hermChartPot_586ea6d2fcc4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:11.119273+00:00
-- url     : https://prove2.me/theorems/9601891c-436d-4b17-beb2-9c4d60e4c5e4
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian cont Diff herm Chart Pot 586ea6d2fcc4: P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian cont Diff herm Chart Pot 586ea6d2fcc4
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian cont Diff herm Chart Pot 586ea6d2fcc4 construction uses the P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian cont Diff herm Chart Pot 586ea6d2fcc4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergySwap.lean#L77-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergySwap.lean#L77-L81

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

theorem P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_contDiff_hermChartPot_586ea6d2fcc4 (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hM : M.PosDef) :
    ContDiff ℝ 2 (hermChartPot M) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergySwapHessian».«contDiff_hermChartPot» := P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_contDiff_hermChartPot_586ea6d2fcc4
