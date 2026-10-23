-- Prove2me | Theorems.Thm_SamplingIPM_Spectra_lemma_3_2
-- name    : SamplingIPM.Spectra.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:22:42.786761+00:00
-- url     : https://prove2.me/theorems/bb04f77a-d2e5-468a-a8e7-60159a283341
-- title:
--   Lemma 3.2, p. 11 — a convex body containing a ball of radius r has λ_min(Σ(0)) ≥ ¼(r/(n+1))²
-- statement:
--   Let $K\subseteq\mathbb R^n$ be a convex body that contains a Euclidean ball of radius $r>0$, and let $\Sigma(0)$ be the covariance matrix of the uniform distribution over $K$. Then the smallest eigenvalue of $\Sigma(0)$ satisfies
--   $$\lambda_{\min}(\Sigma(0))\ \ge\ \frac14\Big(\frac{r}{n+1}\Big)^2,$$
--   that is, $\langle v,\Sigma(0)v\rangle\ge\frac14\big(\frac{r}{n+1}\big)^2\|v\|^2$ for every $v\in\mathbb R^n$.
--
--   This is the base case of the spectral lower bounds in §3.1: Theorem 3.1 transports it from $\theta=0$ to arbitrary $\theta$.
--
--   **Formalization Note** The inner ball is an open ball $\{x:\|x-x_0\|<r\}\subseteq K$; since $K$ is closed this is equivalent to containing the closed ball. "$\lambda_{\min}\ge c$" is the quadratic-form bound for all $v$.
-- source:
--   Badenbroek & de Klerk, Complexity Analysis of a Sampling-Based Interior Point Method for Convex Optimization, arXiv:1811.07677v1, p. 11, Lemma 3.2

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_ExpFamily

open scoped RealInnerProductSpace
open EntropicBarrier.Universal

namespace SamplingIPM.Spectra

theorem lemma_3_2 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsConvexBody K)
    (x₀ : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r) (hin : Metric.ball x₀ r ⊆ K)
    (v : EuclideanSpace ℝ (Fin n)) :
    (1 / 4) * (r / ((n : ℝ) + 1)) ^ 2 * ‖v‖ ^ 2 ≤ covForm K 0 v v := by sorry

end SamplingIPM.Spectra
