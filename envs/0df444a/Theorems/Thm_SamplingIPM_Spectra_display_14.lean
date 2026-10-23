-- Prove2me | Theorems.Thm_SamplingIPM_Spectra_display_14
-- name    : SamplingIPM.Spectra.display_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:43.375994+00:00
-- url     : https://prove2.me/theorems/fb69b762-fbbd-4e0d-96a3-292b88a000a4
-- title:
--   Display (14), p. 11 — for ‖θ‖ ≤ 1/(4R), ‖v‖_θ ≥ ¼ (r/(n+1)) ‖v‖
-- statement:
--   Let $K\subseteq\mathbb R^n$ be a convex body that contains a Euclidean ball of radius $r>0$ and is contained in a closed Euclidean ball of radius $R$, and let $\|v\|_\theta=\sqrt{\langle v,\Sigma(\theta)v\rangle}$ be the local norm of the Boltzmann covariance. If $\theta\in\mathbb R^n$ satisfies $\|\theta\|\le\frac1{4R}$, then
--   $$\|\theta-0\|_0\le\frac12,$$
--   and for every $v\in\mathbb R^n$
--   $$\|v\|_\theta\ \ge\ \frac14\,\frac{r}{n+1}\,\|v\| .$$
--
--   This is the small-parameter case of the proof of Theorem 3.1; squaring it gives the first bound of Theorem 3.1, and it is applied again at the end of the halving chain.
--
--   **Formalization Note** $\|\theta-0\|_0$ is written $\|\theta\|_0$. The inner ball is open (equivalent for closed $K$).
-- source:
--   Badenbroek & de Klerk, Complexity Analysis of a Sampling-Based Interior Point Method for Convex Optimization, arXiv:1811.07677v1, p. 11, proof of Theorem 3.1, display (14)

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_ExpFamily
import Definitions.Def_SamplingIPM_Spectra_Model

open scoped RealInnerProductSpace
open EntropicBarrier.Universal

namespace SamplingIPM.Spectra

theorem display_14 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsConvexBody K)
    (x₀ y₀ : EuclideanSpace ℝ (Fin n)) (r R : ℝ) (hr : 0 < r)
    (hin : Metric.ball x₀ r ⊆ K) (hout : K ⊆ Metric.closedBall y₀ R)
    (θ : EuclideanSpace ℝ (Fin n)) (hθ : ‖θ‖ ≤ 1 / (4 * R)) :
    localNorm K 0 θ ≤ 1 / 2 ∧
      ∀ v : EuclideanSpace ℝ (Fin n), (1 / 4) * (r / ((n : ℝ) + 1)) * ‖v‖ ≤ localNorm K θ v := by sorry

end SamplingIPM.Spectra
