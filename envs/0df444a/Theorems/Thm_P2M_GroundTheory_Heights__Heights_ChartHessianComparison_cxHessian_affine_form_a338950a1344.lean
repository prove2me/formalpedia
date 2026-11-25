-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_cxHessian_affine_form_a338950a1344
-- name    : P2M_GroundTheory_Heights__Heights_ChartHessianComparison_cxHessian_affine_form_a338950a1344
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:27:39.060551+00:00
-- url     : https://prove2.me/theorems/90784757-70f2-4c4f-895a-1cb457eb5146
-- title:
--   P2 M Ground Theory Heights  Heights Chart Hessian Comparison cx Hessian affine form a338950a1344: P2 M Ground Theory Heights  Heights Chart Hessian Comparison cx Hessian affine form a338950a1344
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Hessian Comparison cx Hessian affine form a338950a1344 construction uses the P2 M Ground Theory Heights  Heights Chart Hessian Comparison cx Hessian affine form a338950a1344 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L88-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L88-L98

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

theorem P2M_GroundTheory_Heights__Heights_ChartHessianComparison_cxHessian_affine_form_a338950a1344 [CompleteSpace F] (c : F) (L : (Fin e → ℂ) →L[ℂ] F) (y x : Fin e → ℂ)
    (h0 : c + L y ≠ 0) :
    star x ⬝ᵥ (cxHessian (fun y' => 2⁻¹ * Real.log (⟪c + L y', c + L y'⟫_ℂ).re) y *ᵥ x) =
      ((‖L (star x) - (⟪c + L y, L (star x)⟫_ℂ / ⟪c + L y, c + L y⟫_ℂ) • (c + L y)‖ ^ 2 /
        (2 * ‖c + L y‖ ^ 2) : ℝ) : ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartHessianComparison».«cxHessian_affine_form» := P2M_GroundTheory_Heights__Heights_ChartHessianComparison_cxHessian_affine_form_a338950a1344
