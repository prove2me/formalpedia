-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hess_isHermitian_36e14e4d0526
-- name    : P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hess_isHermitian_36e14e4d0526
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:57.868186+00:00
-- url     : https://prove2.me/theorems/e025e324-ade9-4bfa-af3e-d182d0840afb
-- title:
--   P2 M Ground Theory Heights  Heights Chart Hessian Comparison hess is Hermitian 36e14e4d0526: P2 M Ground Theory Heights  Heights Chart Hessian Comparison hess is Hermitian 36e14e4d0526
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Hessian Comparison hess is Hermitian 36e14e4d0526 construction uses the P2 M Ground Theory Heights  Heights Chart Hessian Comparison hess is Hermitian 36e14e4d0526 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L181-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L181-L184

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

theorem P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hess_isHermitian_36e14e4d0526 (hB : B.det ≠ 0) (y : Fin e → ℂ) :
    (cxHessian (hermChartPot (Bᴴ * B)) y).IsHermitian := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartHessianComparison».«hess_isHermitian» := P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hess_isHermitian_36e14e4d0526
