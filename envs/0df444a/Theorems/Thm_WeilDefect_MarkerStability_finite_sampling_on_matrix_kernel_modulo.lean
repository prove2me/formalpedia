-- Prove2me | Theorems.Thm_WeilDefect_MarkerStability_finite_sampling_on_matrix_kernel_modulo
-- name    : WeilDefect.MarkerStability.finite_sampling_on_matrix_kernel_modulo
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T18:16:35.8+00:00
-- url     : https://prove2.me/theorems/07b3dfcf-e1b2-43dd-b35b-5c525c971fc2
-- title:
--   Matrix-kernel sampling modulo known null directions has the dimension-difference bound
-- statement:
--   For original finite complex matrices $K,H$ with $\ker H\subseteq\ker K$, and original supplied rows that all vanish on $\ker H$, ONE original sampling set $G$ has $$|G|\le\dim\ker K-\dim\ker H.$$ For EVERY coefficient $c$ with $Kc=0$, its selected row vanishing is equivalent to ALL supplied row vanishing. Both null-space hypotheses are explicit. No row injectivity or nonsingular Gram matrix is assumed.
-- source:
--   monocap-tech/weil, compiling source 2aef23a3fe056f7d73b4b52a6baf35b6453d9b0b, exact declaration WeilDefect.MarkerStability.finite_sampling_on_matrix_kernel_modulo

import Mathlib.Data.Complex.Basic
import Theorems.Thm_WeilDefect_MarkerStability_finite_functionals_determine_all
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

import Theorems.Thm_WeilDefect_MarkerStability_finite_functionals_modulo_submodule
set_option autoImplicit false
open Matrix
open scoped Classical
noncomputable section
open WeilDefect.MarkerStability

theorem WeilDefect.MarkerStability.finite_sampling_on_matrix_kernel_modulo
    {I Ω : Type*} [Fintype I] (K H : Matrix I I ℂ) (r : Ω → (I → ℂ))
    (hHK : LinearMap.ker H.mulVecLin ≤ LinearMap.ker K.mulVecLin)
    (hr : ∀ ρ c, H *ᵥ c = 0 → r ρ ⬝ᵥ c = 0) :
    ∃ G : Finset Ω,
      G.card ≤ Module.finrank ℂ (LinearMap.ker K.mulVecLin) -
        Module.finrank ℂ (LinearMap.ker H.mulVecLin) ∧
      ∀ c : I → ℂ, K *ᵥ c = 0 →
        ((∀ ρ ∈ G, r ρ ⬝ᵥ c = 0) ↔ ∀ ρ : Ω, r ρ ⬝ᵥ c = 0) := by sorry
