-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hermChartPot_eq_b52d42d77135
-- name    : P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hermChartPot_eq_b52d42d77135
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:24.319003+00:00
-- url     : https://prove2.me/theorems/bf265fc6-3e17-4481-bbb1-70a60558868b
-- title:
--   P2 M Ground Theory Heights  Heights Chart Hessian Comparison herm Chart Pot eq b52d42d77135: P2 M Ground Theory Heights  Heights Chart Hessian Comparison herm Chart Pot eq b52d42d77135
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Hessian Comparison herm Chart Pot eq b52d42d77135 construction uses the P2 M Ground Theory Heights  Heights Chart Hessian Comparison herm Chart Pot eq b52d42d77135 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L157-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L157-L163

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramHess
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix
open scoped ComplexOrder InnerProductSpace
noncomputable section
open GroundTheory.Heights₂.Heights.ChartHessianComparison
variable {e : ℕ} (B : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)

theorem P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hermChartPot_eq_b52d42d77135 :
    hermChartPot (Bᴴ * B) = fun y => 2⁻¹ * Real.log (⟪chartConst B + chartLin B y, chartConst B + chartLin B y⟫_ℂ).re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartHessianComparison».«hermChartPot_eq» := P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hermChartPot_eq_b52d42d77135
