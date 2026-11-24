-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_chart_add_96698a2c7bee
-- name    : P2M_GroundTheory_Heights__Heights_ChartHessianComparison_chart_add_96698a2c7bee
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:12.433113+00:00
-- url     : https://prove2.me/theorems/dbfc6148-ad82-4e2b-9179-1525029cb513
-- title:
--   P2 M Ground Theory Heights  Heights Chart Hessian Comparison chart add 96698a2c7bee: P2 M Ground Theory Heights  Heights Chart Hessian Comparison chart add 96698a2c7bee
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Hessian Comparison chart add 96698a2c7bee construction uses the P2 M Ground Theory Heights  Heights Chart Hessian Comparison chart add 96698a2c7bee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L125-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L125-L129

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

theorem P2M_GroundTheory_Heights__Heights_ChartHessianComparison_chart_add_96698a2c7bee (y : Fin e → ℂ) :
    chartConst B + chartLin B y = WithLp.toLp 2 (B *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartHessianComparison».«chart_add» := P2M_GroundTheory_Heights__Heights_ChartHessianComparison_chart_add_96698a2c7bee
