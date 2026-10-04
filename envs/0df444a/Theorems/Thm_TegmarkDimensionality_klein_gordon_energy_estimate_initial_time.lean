-- Prove2me | Theorems.Thm_TegmarkDimensionality_klein_gordon_energy_estimate_initial_time
-- name    : TegmarkDimensionality.klein_gordon_energy_estimate_initial_time
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T03:28:36.281476+00:00
-- url     : https://prove2.me/theorems/8ad59875-1c38-4cea-a3f4-ad447777c455
-- title:
--   Klein–Gordon energy bound at $t=0$ (equality)
-- statement:
--   For a $C^2$ solution of the Klein–Gordon equation on $\mathbb R\times\mathbb R^n$, at the initial time $t=0$ the finite-speed energy bound compares the same ball $B(x_0,R)$ on both sides and holds with equality (the integrands coincide). This is the base case for an induction on time in a full finite-speed propagation proof.
-- source:
--   M. Tegmark, Class. Quantum Grav. 14 (1997) L69–L75, p. L73 (hyperbolic well-posedness); base case of the energy method

import Mathlib
import Definitions.Def_tegmark_laplacian
open MeasureTheory

namespace TegmarkDimensionality

/-- At `t = 0`, the Klein–Gordon energy inequality on the ball of radius `R` is an
equality: both sides integrate the same energy density over `B(x_0,R)`. -/
theorem klein_gordon_energy_estimate_initial_time (n : ℕ) (μ : ℝ)
    (u : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : ContDiff ℝ 2 (fun p : ℝ × EuclideanSpace ℝ (Fin n) => u p.1 p.2))
    (hKG : ∀ t x, deriv (fun s => deriv (fun s' => u s' x) s) t =
      laplacian (u t) x - μ ^ 2 * u t x)
    (x₀ : EuclideanSpace ℝ (Fin n)) (R t : ℝ) (_ht : |t| ≤ R) (ht0 : t = 0) :
    ∫ x in Metric.ball x₀ (R - |t|),
        ((deriv (fun s => u s x) t) ^ 2 + ‖fderiv ℝ (u t) x‖ ^ 2 + μ ^ 2 * (u t x) ^ 2) ≤
      ∫ x in Metric.ball x₀ R,
        ((deriv (fun s => u s x) 0) ^ 2 + ‖fderiv ℝ (u 0) x‖ ^ 2 + μ ^ 2 * (u 0 x) ^ 2) := by sorry

end TegmarkDimensionality
