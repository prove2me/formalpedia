-- Prove2me | Theorems.Thm_RoughSurfaceScattering_harmonic_analytic_R3
-- name    : RoughSurfaceScattering.harmonic_analytic_R3
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T05:48:47.117028+00:00
-- url     : https://prove2.me/theorems/13c45338-d894-4187-8874-569c90c4aa72
-- title:
--   Harmonic functions on $\mathbb R^3$ are real analytic
-- statement:
--   Let $f:\mathbb R^3\to\mathbb C$ be harmonic at $x$: $f$ is $C^2$ near $x$ and
--
--   $$\Delta f=\partial_1^2f+\partial_2^2f+\partial_3^2f=0\quad\text{in a neighbourhood of }x .$$
--
--   Then $f$ is real analytic at $x$: near $x$ it equals a convergent power series in $y-x$.
--
--   This is the classical analyticity of harmonic functions, in three variables. Through the method of descent, $u(x_1,x_2)e^{kx_3}$, it yields the analyticity of solutions of the two-dimensional Helmholtz equation. That analyticity is used for the extension of near-field data and for unique continuation in the proof of Theorem 6.1 of Wu–Yang (arXiv:2406.06129v2).
--
--   **Formalization Note** Harmonicity is Mathlib's `InnerProductSpace.HarmonicAt`. Mathlib currently proves analyticity only for real-valued harmonic functions on $\mathbb C$.
-- source:
--   Classical: harmonic functions are real analytic, e.g. L. C. Evans, Partial Differential Equations, 2nd ed., §2.2.3, Theorem 10; D. Gilbarg and N. Trudinger, Elliptic PDE of Second Order, Theorem 2.10. Mathlib proves this for ℂ → ℝ (`HarmonicAt.analyticAt`) and lists the general finite-dimensional case as a TODO.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem harmonic_analytic_R3 (f : EuclideanSpace ℝ (Fin 3) → ℂ) (x : EuclideanSpace ℝ (Fin 3))
    (hf : InnerProductSpace.HarmonicAt f x) : AnalyticAt ℝ f x := by sorry

end RoughSurfaceScattering
