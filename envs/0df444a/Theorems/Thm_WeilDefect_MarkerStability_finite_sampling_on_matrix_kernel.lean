-- Prove2me | Theorems.Thm_WeilDefect_MarkerStability_finite_sampling_on_matrix_kernel
-- name    : WeilDefect.MarkerStability.finite_sampling_on_matrix_kernel
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T17:27:06.508662+00:00
-- url     : https://prove2.me/theorems/4e5cc3e4-9f4d-4b59-a543-593d959d4478
-- title:
--   Finite sampling on the original matrix kernel uses at most its dimension
-- statement:
--   For ANY finite complex matrix $K$ and any supplied row family $R_\rho$, there exists ONE finite set $G$ of original row indices, with $|G|\le\dim\ker K$, such that for EVERY $c$ satisfying $Kc=0$, vanishing of the rows in $G$ is equivalent to vanishing of ALL supplied rows. Restrict the original rows to the ORIGINAL matrix kernel; no matrix or row normalization changes and no injectivity is assumed.
-- source:
--   monocap-tech/weil, compiling source ae5ede91582c6434b1676f98d416b23316942daa, exact declaration WeilDefect.MarkerStability.finite_sampling_on_matrix_kernel

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

import Theorems.Thm_WeilDefect_MarkerStability_finite_functionals_determine_all
set_option autoImplicit false
open Matrix
open scoped Classical
noncomputable section
open WeilDefect.MarkerStability

theorem WeilDefect.MarkerStability.finite_sampling_on_matrix_kernel
    {I Ω : Type*} [Fintype I] (K : Matrix I I ℂ) (r : Ω → (I → ℂ)) :
    ∃ G : Finset Ω, G.card ≤ Module.finrank ℂ (LinearMap.ker K.mulVecLin) ∧
      ∀ c : I → ℂ, K *ᵥ c = 0 →
        ((∀ ρ ∈ G, r ρ ⬝ᵥ c = 0) ↔ ∀ ρ : Ω, r ρ ⬝ᵥ c = 0) := by sorry
