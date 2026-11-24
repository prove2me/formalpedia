-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_chart_sub_7e40b2989709
-- name    : P2M_GroundTheory_Heights__Heights_ChartHessianComparison_chart_sub_7e40b2989709
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:26.441023+00:00
-- url     : https://prove2.me/theorems/4e2d5667-b9e4-4101-b077-1ada57e5a230
-- title:
--   P2 M Ground Theory Heights  Heights Chart Hessian Comparison chart sub 7e40b2989709: P2 M Ground Theory Heights  Heights Chart Hessian Comparison chart sub 7e40b2989709
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Hessian Comparison chart sub 7e40b2989709 construction uses the P2 M Ground Theory Heights  Heights Chart Hessian Comparison chart sub 7e40b2989709 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L131-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L131-L134

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

theorem P2M_GroundTheory_Heights__Heights_ChartHessianComparison_chart_sub_7e40b2989709 (y z : Fin e → ℂ) (t : ℂ) :
    chartLin B z - t • (chartConst B + chartLin B y) =
      WithLp.toLp 2 (B *ᵥ ((Fin.cons 0 z : Fin (e + 1) → ℂ) - t • Fin.cons 1 y)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartHessianComparison».«chart_sub» := P2M_GroundTheory_Heights__Heights_ChartHessianComparison_chart_sub_7e40b2989709
