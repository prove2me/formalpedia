-- Prove2me | Theorems.Thm_SpherePacking_ForMathlib_Fourier_fourier_precompose_linear_equivalence
-- name    : SpherePacking.ForMathlib.Fourier.fourier_precompose_linear_equivalence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:03.954123+00:00
-- url     : https://prove2.me/theorems/8256a9fe-039a-426d-9901-a1721578d489
-- title:
--   SpherePacking.ForMathlib.Fourier.fourier_precompose_linear_equivalence
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open SpherePacking SpherePacking.ForMathlib SpherePacking.ForMathlib.Fourier
open scoped FourierTransform
open MeasureTheory
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem SpherePacking.ForMathlib.Fourier.fourier_precompose_linear_equivalence (A : V ≃ₗ[ℝ] V) (f : V → ℂ) (w : V) :
    𝓕 (fun x ↦ f (A x)) w =
      (abs (LinearMap.det (A : V →ₗ[ℝ] V)))⁻¹ •
        𝓕 f (((A.symm : V ≃ₗ[ℝ] V).toLinearMap).adjoint w) := by sorry
