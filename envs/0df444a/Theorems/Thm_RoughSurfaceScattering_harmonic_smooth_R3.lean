-- Prove2me | Theorems.Thm_RoughSurfaceScattering_harmonic_smooth_R3
-- name    : RoughSurfaceScattering.harmonic_smooth_R3
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T06:11:57.365936+00:00
-- url     : https://prove2.me/theorems/fc3573be-f833-4d6a-b797-99f17418babd
-- title:
--   Harmonic functions on open subsets of $\mathbb R^3$ are $C^\infty$
-- statement:
--   Let $U\subseteq\mathbb R^3$ be open and let $f:U\to\mathbb C$ be harmonic on $U$: $f$ is $C^2$ near every point of $U$ and $\Delta f=0$ there. Then
--
--   $$f\in C^n(U)\qquad\text{for every }n\in\mathbb N .$$
--
--   This is Weyl-type regularity for the Laplace equation. Harmonic functions satisfy the mean-value property, so they equal their own mollifications on slightly smaller sets, and mollifications are smooth.
--
--   **Formalization Note** Harmonicity is `InnerProductSpace.HarmonicOnNhd`. Smoothness is stated as `ContDiffOn ℝ n f U` for each natural number $n$.
-- source:
--   L. C. Evans, Partial Differential Equations, 2nd ed., §2.2.3, Theorem 6 (smoothness of harmonic functions, via the mean-value property and mollification).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem harmonic_smooth_R3 (f : EuclideanSpace ℝ (Fin 3) → ℂ)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : IsOpen U)
    (hf : InnerProductSpace.HarmonicOnNhd f U) :
    ∀ n : ℕ, ContDiffOn ℝ n f U := by sorry

end RoughSurfaceScattering
