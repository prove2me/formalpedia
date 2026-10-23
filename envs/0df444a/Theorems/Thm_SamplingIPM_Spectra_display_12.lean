-- Prove2me | Theorems.Thm_SamplingIPM_Spectra_display_12
-- name    : SamplingIPM.Spectra.display_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:22:44.492636+00:00
-- url     : https://prove2.me/theorems/e3d7dbfe-23b0-4863-8841-328d34635605
-- title:
--   Display (12), p. 10 — λ_max(Σ(θ)) ≤ (2R)² for a convex body in a ball of radius R
-- statement:
--   Let $K\subseteq\mathbb R^n$ be a convex body (compact, convex, with non-empty interior) contained in a closed Euclidean ball of radius $R$. For $\theta\in\mathbb R^n$ let $\Sigma(\theta)$ be the covariance of the Boltzmann distribution over $K$ with parameter $\theta$. Then the largest eigenvalue of $\Sigma(\theta)$ is at most $(2R)^2$: for every $\theta\in\mathbb R^n$ and every $v\in\mathbb R^n$,
--   $$\langle v,\Sigma(\theta)v\rangle=\mathbb E_\theta\big[\langle X-\mathbb E_\theta[X],v\rangle^2\big]\le(2R)^2\,\|v\|^2 .$$
--
--   This trivial upper bound on the spectrum is used in the proof of Theorem 3.1 to show that a small parameter $\theta$ is close to $0$ in the local norm at $0$.
--
--   **Formalization Note** "$\lambda_{\max}(\Sigma(\theta))\le c$" is stated as the quadratic-form bound $\langle v,\Sigma(\theta)v\rangle\le c\|v\|^2$ for all $v$, which is the paper's characterization $\lambda_{\max}(A)=\max_{\|v\|=1}\langle v,Av\rangle$ extended by homogeneity.
-- source:
--   Badenbroek & de Klerk, Complexity Analysis of a Sampling-Based Interior Point Method for Convex Optimization, arXiv:1811.07677v1, p. 10, display (12)

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_ExpFamily

open scoped RealInnerProductSpace
open EntropicBarrier.Universal

namespace SamplingIPM.Spectra

theorem display_12 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsConvexBody K)
    (y₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ) (hout : K ⊆ Metric.closedBall y₀ R)
    (θ v : EuclideanSpace ℝ (Fin n)) :
    covForm K θ v v ≤ (2 * R) ^ 2 * ‖v‖ ^ 2 := by sorry

end SamplingIPM.Spectra
