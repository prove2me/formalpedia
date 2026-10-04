-- Prove2me | Theorems.Thm_TegmarkDimensionality_klein_gordon_localized_energy_antitone
-- name    : TegmarkDimensionality.klein_gordon_localized_energy_antitone
-- status  : Open
-- author  : @moona3k
-- created : 2026-10-04T05:16:24.186289+00:00
-- url     : https://prove2.me/theorems/9bfb3aec-7758-4327-8054-e730b9fb70dd
-- title:
--   Klein–Gordon localized energy is non-increasing in time (finite speed)
-- statement:
--   Let $u$ be a $C^2$ solution of $\partial_t^2 u = \nabla^2 u - \mu^2 u$ on $\mathbb R\times\mathbb R^n$, and let
--   $$E(t)=\int_{|x-x_0|<R-|t|}\bigl((\partial_t u)^2+|\nabla_x u|^2+\mu^2 u^2\bigr)\,dx.$$
--   For $0\le s_1\le s_2\le R$, writing the same integral with time $s_i$ in place of $t$,
--   $$E(s_2)\le E(s_1).$$
--   (Together with time reversal, this yields monotonicity in $|t|$ and the Tegmark cone-of-dependence bound.)
-- source:
--   M. Tegmark, Class. Quantum Grav. 14 (1997) L69–L75, p. L73 (hyperbolic well-posedness; energy method on cones of dependence)

import Mathlib
import Definitions.Def_tegmark_laplacian
open MeasureTheory

namespace TegmarkDimensionality

/-- For a `C²` Klein–Gordon solution, the energy
`E(t) = ∫_{B(x₀,R-|t|)} e(t,x)\,dx` is non-increasing in `|t|` for `|t| ≤ R`
(here `e` is the standard KG energy density). This is the core finite-speed
propagation step behind the cone-of-dependence energy bound. -/
theorem klein_gordon_localized_energy_antitone (n : ℕ) (μ : ℝ)
    (u : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : ContDiff ℝ 2 (fun p : ℝ × EuclideanSpace ℝ (Fin n) => u p.1 p.2))
    (hKG : ∀ t x, deriv (fun s => deriv (fun s' => u s' x) s) t =
      laplacian (u t) x - μ ^ 2 * u t x)
    (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ) (hR : 0 < R)
    {s₁ s₂ : ℝ} (hs₁ : 0 ≤ s₁) (hsle : s₁ ≤ s₂) (hs₂R : s₂ ≤ R) :
    ∫ x in Metric.ball x₀ (R - s₂),
        ((deriv (fun s => u s x) s₂) ^ 2 + ‖fderiv ℝ (u s₂) x‖ ^ 2 + μ ^ 2 * (u s₂ x) ^ 2) ≤
      ∫ x in Metric.ball x₀ (R - s₁),
        ((deriv (fun s => u s x) s₁) ^ 2 + ‖fderiv ℝ (u s₁) x‖ ^ 2 + μ ^ 2 * (u s₁ x) ^ 2) := by sorry

end TegmarkDimensionality
