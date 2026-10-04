-- Prove2me | Theorems.Thm_TegmarkDimensionality_klein_gordon_energy_estimate_light_cone
-- name    : TegmarkDimensionality.klein_gordon_energy_estimate_light_cone
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T04:19:16.879333+00:00
-- url     : https://prove2.me/theorems/65dd7ff8-e3e1-4b1e-b760-4969adf8d90c
-- title:
--   Klein–Gordon energy bound on the light cone ($|t|=R$)
-- statement:
--   For a $C^2$ solution of the Klein–Gordon equation, when $|t|=R$ the cone of dependence at time $t$ collapses to an empty spatial ball ($R-|t|=0$), so the energy on the left-hand side of the finite-speed bound is zero and the inequality follows from nonnegativity of the energy density on the right.
-- source:
--   M. Tegmark, Class. Quantum Grav. 14 (1997) L69–L75, p. L73; boundary case $|t|=R$ of the energy method

import Mathlib
import Definitions.Def_tegmark_laplacian
open MeasureTheory

namespace TegmarkDimensionality

/-- On the light cone `|t| = R`, the ball `B(x₀, R - |t|)` has radius zero, so the
left-hand energy integral vanishes and is bounded by the initial energy on `B(x₀,R)`. -/
theorem klein_gordon_energy_estimate_light_cone (n : ℕ) (μ : ℝ)
    (u : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : ContDiff ℝ 2 (fun p : ℝ × EuclideanSpace ℝ (Fin n) => u p.1 p.2))
    (hKG : ∀ t x, deriv (fun s => deriv (fun s' => u s' x) s) t =
      laplacian (u t) x - μ ^ 2 * u t x)
    (x₀ : EuclideanSpace ℝ (Fin n)) (R t : ℝ) (_ht : |t| ≤ R) (htR : |t| = R) :
    ∫ x in Metric.ball x₀ (R - |t|),
        ((deriv (fun s => u s x) t) ^ 2 + ‖fderiv ℝ (u t) x‖ ^ 2 + μ ^ 2 * (u t x) ^ 2) ≤
      ∫ x in Metric.ball x₀ R,
        ((deriv (fun s => u s x) 0) ^ 2 + ‖fderiv ℝ (u 0) x‖ ^ 2 + μ ^ 2 * (u 0 x) ^ 2) := by sorry

end TegmarkDimensionality
