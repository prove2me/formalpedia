-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_logCoord_re_383796dc332b
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_logCoord_re_383796dc332b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:19:16.935006+00:00
-- url     : https://prove2.me/theorems/7f2247e8-2447-4678-82a7-bcc7a7713d44
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian log Coord re 383796dc332b: P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian log Coord re 383796dc332b
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian log Coord re 383796dc332b construction uses the P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian log Coord re 383796dc332b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergySwap.lean#L95-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergySwap.lean#L95-L99

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

theorem P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_logCoord_re_383796dc332b (y y' : Fin (e + 1) → ℂ) (hy : y 0 ≠ 0) (hy' : y' 0 ≠ 0) :
    (logCoord y y').re = Real.log ‖y' 0‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergySwapHessian».«logCoord_re» := P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_logCoord_re_383796dc332b
