-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_swap_mulVec_cons_039056bdfdb4
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_swap_mulVec_cons_039056bdfdb4
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:18:58.818804+00:00
-- url     : https://prove2.me/theorems/d80a7ac1-d168-4573-8966-42432175bfd7
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian swap mul Vec cons 039056bdfdb4: P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian swap mul Vec cons 039056bdfdb4
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian swap mul Vec cons 039056bdfdb4 construction uses the P2 M Ground Theory Heights  Heights Chart Energy Swap Hessian swap mul Vec cons 039056bdfdb4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergySwap.lean#L33-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergySwap.lean#L33-L48

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

theorem P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_swap_mulVec_cons_039056bdfdb4 (y : Fin (e + 1) → ℂ) (hy : y 0 ≠ 0) :
    swapFirstTwo e *ᵥ (Fin.cons 1 y : Fin (e + 1 + 1) → ℂ) =
      y 0 • (Fin.cons 1 (chartInv y) : Fin (e + 1 + 1) → ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergySwapHessian».«swap_mulVec_cons» := P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_swap_mulVec_cons_039056bdfdb4
