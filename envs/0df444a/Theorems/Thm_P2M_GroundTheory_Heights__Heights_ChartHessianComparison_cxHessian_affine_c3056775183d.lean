-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_cxHessian_affine_c3056775183d
-- name    : P2M_GroundTheory_Heights__Heights_ChartHessianComparison_cxHessian_affine_c3056775183d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:59.790446+00:00
-- url     : https://prove2.me/theorems/90c1b664-9587-4c6f-a1ee-798ccf9bd26b
-- title:
--   P2 M Ground Theory Heights  Heights Chart Hessian Comparison cx Hessian affine c3056775183d: P2 M Ground Theory Heights  Heights Chart Hessian Comparison cx Hessian affine c3056775183d
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Hessian Comparison cx Hessian affine c3056775183d construction uses the P2 M Ground Theory Heights  Heights Chart Hessian Comparison cx Hessian affine c3056775183d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L76-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L76-L86

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
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartHessianComparison_cxHessian_affine_c3056775183d [CompleteSpace F] (c : F) (L : (Fin e → ℂ) →L[ℂ] F) (y : Fin e → ℂ)
    (h0 : c + L y ≠ 0) :
    cxHessian (fun y' => 2⁻¹ * Real.log (⟪c + L y', c + L y'⟫_ℂ).re) y =
      gramHess (c + L y) (fun j => L (Pi.single j 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartHessianComparison».«cxHessian_affine» := P2M_GroundTheory_Heights__Heights_ChartHessianComparison_cxHessian_affine_c3056775183d
