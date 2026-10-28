-- Prove2me | Theorems.Thm_SamplingIPM_Spectra_theorem_3_1
-- name    : SamplingIPM.Spectra.theorem_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:22:51.951137+00:00
-- url     : https://prove2.me/theorems/875cce53-c48f-4a2b-91bb-56bf0dece513
-- title:
--   Theorem 3.1, p. 11 — lower bounds on λ_min(Σ(θ)) for the Boltzmann covariance over a convex body
-- statement:
--   Let $K\subseteq\mathbb R^n$ be a convex body that contains a Euclidean ball of radius $r>0$ and is contained in a Euclidean ball of radius $R$. Let $f(\theta)=\ln\int_K e^{\langle\theta,x\rangle}dx$ be the log partition function of $K$, with $\langle\cdot,\cdot\rangle$ the Euclidean inner product, and let $\Sigma(\theta)$ be its Hessian, which is the covariance matrix of the Boltzmann distribution over $K$ with parameter $\theta$. Let $f^*$ be the entropic barrier for $K$ (the Fenchel conjugate of $f$) with complexity parameter $\vartheta$. Then for every $\theta\in\mathbb R^n$ with $\|\theta\|\le\frac1{4R}$,
--   $$\lambda_{\min}(\Sigma(\theta))\ \ge\ \frac1{16}\Big(\frac r{n+1}\Big)^2,$$
--   and for every $\theta\in\mathbb R^n$ with $\|\theta\|>\frac1{4R}$,
--   $$\lambda_{\min}(\Sigma(\theta))\ \ge\ \frac1{64}\Big(\frac1{4R\|\theta\|}\Big)^{4\sqrt\vartheta+2}\Big(\frac r{n+1}\Big)^2 .$$
--
--   The theorem gives a lower bound on the spectrum of every Boltzmann covariance matrix over $K$, polynomial in $r/(n+1)$ near $\theta=0$ and degrading with $\|\theta\|$ at a rate governed by the complexity parameter. The paper uses it to control the conditioning of the Hessians met by its sampling-based interior point method.
--
--   **Formalization Note** $\Sigma(\theta)$ is the published bilinear form `covForm K θ`, and "$\lambda_{\min}(\Sigma(\theta))\ge c$" is stated as $\langle v,\Sigma(\theta)v\rangle\ge c\|v\|^2$ for all $v$ (the paper's $\lambda_{\min}(A)=\min_{\|v\|=1}\langle v,Av\rangle$, by homogeneity). "Complexity parameter $\vartheta$" is the published predicate `SatisfiesNuBound K (entropicBarrier K) ϑ`, i.e. $Df^*(x)[h]\le\sqrt{\vartheta D^2f^*(x)[h,h]}$ on $\operatorname{int}K$, together with $\vartheta\ge0$. This is equivalent to the paper's reading $\vartheta=\sup_x\|g^*_x(x)\|^{*2}_x$: the sup satisfies the predicate, and the bound for the sup implies it for every larger $\vartheta$ because $1/(4R\|\theta\|)<1$. The inner ball is open (equivalent for closed $K$); the outer ball is closed. The exponent $4\sqrt\vartheta+2$ is a real power.
-- source:
--   Badenbroek & de Klerk, Complexity Analysis of a Sampling-Based Interior Point Method for Convex Optimization, arXiv:1811.07677v1, p. 11, Theorem 3.1

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_ExpFamily
import Definitions.Def_EntropicBarrier_Universal_SelfConcordantBarrier

open scoped RealInnerProductSpace
open EntropicBarrier.Universal

namespace SamplingIPM.Spectra

theorem theorem_3_1 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsConvexBody K)
    (x₀ y₀ : EuclideanSpace ℝ (Fin n)) (r R ϑ : ℝ) (hr : 0 < r)
    (hin : Metric.ball x₀ r ⊆ K) (hout : K ⊆ Metric.closedBall y₀ R)
    (hϑ0 : 0 ≤ ϑ) (hϑ : SatisfiesNuBound K (entropicBarrier K) ϑ)
    (θ : EuclideanSpace ℝ (Fin n)) :
    (‖θ‖ ≤ 1 / (4 * R) →
      ∀ v : EuclideanSpace ℝ (Fin n),
        (1 / 16) * (r / ((n : ℝ) + 1)) ^ 2 * ‖v‖ ^ 2 ≤ covForm K θ v v) ∧
    (1 / (4 * R) < ‖θ‖ →
      ∀ v : EuclideanSpace ℝ (Fin n),
        (1 / 64) * (1 / (4 * R * ‖θ‖)) ^ (4 * Real.sqrt ϑ + 2) * (r / ((n : ℝ) + 1)) ^ 2 * ‖v‖ ^ 2
          ≤ covForm K θ v v) := by sorry

end SamplingIPM.Spectra
