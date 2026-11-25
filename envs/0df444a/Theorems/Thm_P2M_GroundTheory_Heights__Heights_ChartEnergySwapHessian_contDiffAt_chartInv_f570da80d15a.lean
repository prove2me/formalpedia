-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_contDiffAt_chartInv_f570da80d15a
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_contDiffAt_chartInv_f570da80d15a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:18:14.072626+00:00
-- url     : https://prove2.me/theorems/4e229313-f841-4f64-8c4f-f3707feeb483
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian cont Diff At chart Inv f570da80d15a: P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian cont Diff At chart Inv f570da80d15a
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian cont Diff At chart Inv f570da80d15a construction uses the P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian cont Diff At chart Inv f570da80d15a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergySwap.lean#L83-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergySwap.lean#L83-L90

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

theorem P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_contDiffAt_chartInv_f570da80d15a {y : Fin (e + 1) → ℂ} (hy : y 0 ≠ 0) : ContDiffAt ℂ 2 chartInv y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergySwapHessian».«contDiffAt_chartInv» := P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_contDiffAt_chartInv_f570da80d15a
