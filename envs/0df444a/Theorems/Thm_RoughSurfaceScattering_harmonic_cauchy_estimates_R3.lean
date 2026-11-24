-- Prove2me | Theorems.Thm_RoughSurfaceScattering_harmonic_cauchy_estimates_R3
-- name    : RoughSurfaceScattering.harmonic_cauchy_estimates_R3
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T06:02:33.065804+00:00
-- url     : https://prove2.me/theorems/29cb7ae2-1978-4cdb-84d2-503841c83e79
-- title:
--   Cauchy estimates for harmonic functions on $\mathbb R^3$
-- statement:
--   Let $f:\mathbb R^3\to\mathbb C$ be harmonic at $x$: $C^2$ near $x$ with $\Delta f=0$ in a neighbourhood of $x$. Then there are $R>0$, $M\in\mathbb R$ and $\rho>0$ such that $f$ is $C^\infty$ on $B(x,R)$ and
--
--   $$\|D^nf(y)\|\le M\,\frac{n!}{\rho^n}\qquad\text{for all }n\ge0,\ y\in B(x,R).$$
--
--   These are the Cauchy-type estimates for harmonic functions. They follow from the mean-value property: first harmonic functions are smooth, and then each derivative of order $n$ at a point is bounded by $C^n n!\,r^{-n}$ times the $L^1$ norm over a ball. Combined with the criterion `analyticAt_of_iteratedFDeriv_bound`, they give the analyticity of harmonic functions.
--
--   **Formalization Note** Harmonicity is Mathlib's `InnerProductSpace.HarmonicAt`. $D^nf$ is `iteratedFDeriv` with the operator norm.
-- source:
--   L. C. Evans, Partial Differential Equations, 2nd ed., §2.2.3: Theorem 6 (smoothness), Theorem 7 (estimates on derivatives) and the proof of Theorem 10, which derives |D^α u(x)| ≤ M (2^{n+1} n e)^{|α|} |α|! / r^{|α|} from the mean-value property.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem harmonic_cauchy_estimates_R3 (f : EuclideanSpace ℝ (Fin 3) → ℂ)
    (x : EuclideanSpace ℝ (Fin 3)) (hf : InnerProductSpace.HarmonicAt f x) :
    ∃ R > (0 : ℝ), ∃ M ρ : ℝ, 0 < ρ ∧ (∀ n : ℕ, ContDiffOn ℝ n f (Metric.ball x R)) ∧
      ∀ n : ℕ, ∀ y ∈ Metric.ball x R,
        ‖iteratedFDeriv ℝ n f y‖ ≤ M * (n.factorial : ℝ) / ρ ^ n := by sorry

end RoughSurfaceScattering
