-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_chartLin_apply_d879f0c04e2e
-- name    : P2M_GroundTheory_Heights__Heights_ChartHessianComparison_chartLin_apply_d879f0c04e2e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:12.465498+00:00
-- url     : https://prove2.me/theorems/42c6110c-9b10-41fe-8218-612e8de50e24
-- title:
--   P2 M Ground Theory Heights  Heights Chart Hessian Comparison chart Lin apply d879f0c04e2e: P2 M Ground Theory Heights  Heights Chart Hessian Comparison chart Lin apply d879f0c04e2e
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Hessian Comparison chart Lin apply d879f0c04e2e construction uses the P2 M Ground Theory Heights  Heights Chart Hessian Comparison chart Lin apply d879f0c04e2e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L119-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L119-L120

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

theorem P2M_GroundTheory_Heights__Heights_ChartHessianComparison_chartLin_apply_d879f0c04e2e (y : Fin e → ℂ) :
    chartLin B y = WithLp.toLp 2 (B *ᵥ (Fin.cons 0 y : Fin (e + 1) → ℂ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartHessianComparison».«chartLin_apply» := P2M_GroundTheory_Heights__Heights_ChartHessianComparison_chartLin_apply_d879f0c04e2e
