-- Prove2me | Theorems.Thm_TegmarkDimensionality_klein_gordon_energy_estimate_interior_positive_time
-- name    : TegmarkDimensionality.klein_gordon_energy_estimate_interior_positive_time
-- status  : Open
-- author  : @moona3k
-- created : 2026-10-04T08:24:54.606986+00:00
-- url     : https://prove2.me/theorems/d218cb5e-4620-4b40-b0c4-6eca8ca8e904
-- title:
--   Klein–Gordon interior energy bound for $0 < t < R$
-- statement:
--   For a $C^2$ Klein–Gordon solution and $0 < t < R$ with $|t| \le R$, the energy on the ball of radius $R-|t|$ at time $t$ is bounded by the initial energy on $B(x_0,R)$. This is the positive-time half of the interior light-cone estimate.
-- source:
--   Decomposition of TegmarkDimensionality.klein_gordon_energy_estimate_interior; see Tegmark 1997 mission

import Mathlib
import Definitions.Def_tegmark_laplacian
open MeasureTheory

namespace TegmarkDimensionality

/-- Interior cone-of-dependence energy inequality for positive time; follows from
`klein_gordon_localized_energy_antitone` by taking $s_1=0$, $s_2=t$. -/
theorem klein_gordon_energy_estimate_interior_positive_time (n : ℕ) (μ : ℝ)
    (u : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : ContDiff ℝ 2 (fun p : ℝ × EuclideanSpace ℝ (Fin n) => u p.1 p.2))
    (hKG : ∀ t x, deriv (fun s => deriv (fun s' => u s' x) s) t =
      laplacian (u t) x - μ ^ 2 * u t x)
    (x₀ : EuclideanSpace ℝ (Fin n)) (R t : ℝ) (ht : |t| ≤ R)
    (htpos : 0 < t) (htR : t < R) :
    ∫ x in Metric.ball x₀ (R - |t|),
        ((deriv (fun s => u s x) t) ^ 2 + ‖fderiv ℝ (u t) x‖ ^ 2 + μ ^ 2 * (u t x) ^ 2) ≤
      ∫ x in Metric.ball x₀ R,
        ((deriv (fun s => u s x) 0) ^ 2 + ‖fderiv ℝ (u 0) x‖ ^ 2 + μ ^ 2 * (u 0 x) ^ 2) := by sorry

end TegmarkDimensionality
