-- Prove2me | Theorems.Thm_RoughSurfaceScattering_harmonic_iteratedFDeriv_R3
-- name    : RoughSurfaceScattering.harmonic_iteratedFDeriv_R3
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T06:11:40.478031+00:00
-- url     : https://prove2.me/theorems/9e5d2139-fe39-492b-b469-f4a1694e6e32
-- title:
--   All derivatives of a harmonic function on $\mathbb R^3$ are harmonic
-- statement:
--   Let $U\subseteq\mathbb R^3$ be open and $f:U\to\mathbb C$ harmonic on $U$. Then for every $n$ the $n$-th derivative
--
--   $$D^nf:U\to\mathcal L^n(\mathbb R^3;\mathbb C)$$
--
--   is harmonic on $U$, as a function with values in the Banach space of continuous $n$-linear maps.
--
--   Since $f$ is smooth, the Laplacian commutes with differentiation: $\Delta(D^nf)=D^n(\Delta f)=0$. This lets mean-value estimates be applied to all derivatives, which is the induction step in the Cauchy estimates for harmonic functions.
--
--   **Formalization Note** $D^nf$ is `iteratedFDeriv ℝ n f`, and harmonicity of vector-valued functions is `InnerProductSpace.HarmonicOnNhd`.
-- source:
--   L. C. Evans, Partial Differential Equations, 2nd ed., §2.2.3, proof of Theorem 7 (derivatives of harmonic functions are harmonic, since the Laplacian commutes with differentiation).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem harmonic_iteratedFDeriv_R3 (f : EuclideanSpace ℝ (Fin 3) → ℂ)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : IsOpen U)
    (hf : InnerProductSpace.HarmonicOnNhd f U) :
    ∀ n : ℕ, InnerProductSpace.HarmonicOnNhd (iteratedFDeriv ℝ n f) U := by sorry

end RoughSurfaceScattering
