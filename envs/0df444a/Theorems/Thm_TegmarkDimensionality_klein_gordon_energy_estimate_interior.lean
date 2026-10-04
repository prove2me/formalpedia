-- Prove2me | Theorems.Thm_TegmarkDimensionality_klein_gordon_energy_estimate_interior
-- name    : TegmarkDimensionality.klein_gordon_energy_estimate_interior
-- status  : Open
-- author  : @moona3k
-- created : 2026-10-04T05:16:34.064203+00:00
-- url     : https://prove2.me/theorems/e0c4b5aa-8da3-45e9-83d3-bb30fcea1c13
-- title:
--   Klein–Gordon energy bound in the interior of the light cone
-- statement:
--   For a $C^2$ Klein–Gordon solution, if $0<|t|<R$ then the energy on the ball of radius $R-|t|$ at time $t$ is bounded by the initial energy on $B(x_0,R)$ at $t=0$.
-- source:
--   M. Tegmark, Class. Quantum Grav. 14 (1997) L69–L75, p. L73

import Mathlib
import Definitions.Def_tegmark_laplacian
open MeasureTheory

namespace TegmarkDimensionality

/-- Strictly inside the light cone (`0 < |t| < R`), the Klein–Gordon finite-speed energy
inequality holds; this is the analytic core once the boundary cases `t = 0` and `|t| = R`
are treated separately. -/
theorem klein_gordon_energy_estimate_interior (n : ℕ) (μ : ℝ)
    (u : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : ContDiff ℝ 2 (fun p : ℝ × EuclideanSpace ℝ (Fin n) => u p.1 p.2))
    (hKG : ∀ t x, deriv (fun s => deriv (fun s' => u s' x) s) t =
      laplacian (u t) x - μ ^ 2 * u t x)
    (x₀ : EuclideanSpace ℝ (Fin n)) (R t : ℝ) (ht : |t| ≤ R)
    (hint : 0 < |t| ∧ |t| < R) :
    ∫ x in Metric.ball x₀ (R - |t|),
        ((deriv (fun s => u s x) t) ^ 2 + ‖fderiv ℝ (u t) x‖ ^ 2 + μ ^ 2 * (u t x) ^ 2) ≤
      ∫ x in Metric.ball x₀ R,
        ((deriv (fun s => u s x) 0) ^ 2 + ‖fderiv ℝ (u 0) x‖ ^ 2 + μ ^ 2 * (u 0 x) ^ 2) := by sorry

end TegmarkDimensionality
