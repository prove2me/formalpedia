-- Prove2me | Theorems.Thm_TegmarkDimensionality_klein_gordon_energy_estimate
-- name    : TegmarkDimensionality.klein_gordon_energy_estimate
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T09:35:40.2366+00:00
-- url     : https://prove2.me/theorems/30efecdc-c904-4397-9cef-eb99a07a8980
-- title:
--   Klein–Gordon initial-value problem: energy estimate on the cones of dependence
-- statement:
--   Let $n\ge0$, $\mu\in\mathbb R$, and let $u(t,x)$ be a $C^2$ solution on $\mathbb R\times\mathbb R^n$ of the Klein–Gordon equation
--   $$\partial_t^2u=\nabla^2u-\mu^2u.$$
--   Let $e(t,x)=(\partial_tu)^2+|\nabla_xu|^2+\mu^2u^2$ be the energy density. Then for every $x_0\in\mathbb R^n$ and all $t,R$ with $|t|\le R$,
--   $$\int_{|x-x_0|<R-|t|}e(t,x)\,dx\;\le\;\int_{|x-x_0|<R}e(0,x)\,dx.$$
--
--   The data $(u,\partial_tu)$ at $t=0$ on the disk $|x-x_0|<R$ therefore control the solution, with finite error bars, throughout the two cones $|x-x_0|<R-|t|$ (future and past). Applied to the difference of two solutions, the inequality shows that such data determine the solution uniquely in those cones. This is the well-posedness of the hyperbolic initial-value problem described in the paper.
-- source:
--   M. Tegmark, *On the dimensionality of spacetime*, Class. Quantum Grav. 14 (1997) L69–L75, https://doi.org/10.1088/0264-9381/14/4/002, p. L73, sixth paragraph ('Hyperbolic equations ... allow well-posed initial-value problems ... specifying initial data (u and u̇) for the Klein–Gordon equation on the shaded disk in figure 3 determines the solution in the volumes bounded by the two cones')

import Mathlib
import Definitions.Def_tegmark_laplacian
open MeasureTheory

namespace TegmarkDimensionality

/-- Well-posedness of the initial-value problem for the Klein–Gordon equation
`u_tt = ∇²u - μ² u` on `ℝ × ℝⁿ`: the energy of a `C²` solution in the ball of radius
`R - |t|` about `x₀` at time `t` is bounded by the energy of the initial data in the ball
of radius `R` about `x₀`, for `|t| ≤ R`.  In particular the data `(u, u_t)` on the disk
`|x - x₀| < R` at `t = 0` determine `u` in the two cones `|x - x₀| < R - |t|`. -/
theorem klein_gordon_energy_estimate (n : ℕ) (μ : ℝ)
    (u : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : ContDiff ℝ 2 (fun p : ℝ × EuclideanSpace ℝ (Fin n) => u p.1 p.2))
    (hKG : ∀ t x, deriv (fun s => deriv (fun s' => u s' x) s) t =
      laplacian (u t) x - μ ^ 2 * u t x)
    (x₀ : EuclideanSpace ℝ (Fin n)) (R t : ℝ) (ht : |t| ≤ R) :
    ∫ x in Metric.ball x₀ (R - |t|),
        ((deriv (fun s => u s x) t) ^ 2 + ‖fderiv ℝ (u t) x‖ ^ 2 + μ ^ 2 * (u t x) ^ 2) ≤
      ∫ x in Metric.ball x₀ R,
        ((deriv (fun s => u s x) 0) ^ 2 + ‖fderiv ℝ (u 0) x‖ ^ 2 + μ ^ 2 * (u 0 x) ^ 2) := by sorry

end TegmarkDimensionality
