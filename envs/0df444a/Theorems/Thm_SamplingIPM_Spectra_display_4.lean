-- Prove2me | Theorems.Thm_SamplingIPM_Spectra_display_4
-- name    : SamplingIPM.Spectra.display_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:32.659529+00:00
-- url     : https://prove2.me/theorems/23e40691-7abe-4d77-af3e-ce440e4565d4
-- title:
--   Display (4), p. 3 — self-concordance of the log partition function in local norms
-- statement:
--   Let $K\subseteq\mathbb R^n$ be a convex body, let $f(\theta)=\ln\int_K e^{\langle\theta,x\rangle}dx$ be its log partition function, and let $\|v\|_\theta=\sqrt{\langle v,\Sigma(\theta)v\rangle}$ be the local norm given by the Hessian $\Sigma(\theta)$ of $f$ (the covariance of the Boltzmann distribution with parameter $\theta$). For all $\theta_0,\theta_1\in\mathbb R^n$ with $\|\theta_1-\theta_0\|_{\theta_0}<1$ and all non-zero $v\in\mathbb R^n$,
--   $$1-\|\theta_1-\theta_0\|_{\theta_0}\ \le\ \frac{\|v\|_{\theta_1}}{\|v\|_{\theta_0}}\ \le\ \frac{1}{1-\|\theta_1-\theta_0\|_{\theta_0}} .$$
--
--   This is the consequence of Definition 2.1 for $f$, which is self-concordant by Bubeck and Eldan. It lets the proof of Theorem 3.1 compare local norms at nearby parameters.
--
--   **Formalization Note** The ratio inequalities are stated in cross-multiplied form, $(1-\|\theta_1-\theta_0\|_{\theta_0})\|v\|_{\theta_0}\le\|v\|_{\theta_1}$ and $\|v\|_{\theta_1}\le\|v\|_{\theta_0}/(1-\|\theta_1-\theta_0\|_{\theta_0})$; this is equivalent to the ratio form because $\Sigma(\theta_0)$ is positive definite for a convex body, and avoids a division by $\|v\|_{\theta_0}$. The hypothesis $v\neq0$ is kept as printed. Definition 2.1's clause "$\theta_1\in\operatorname{dom} f$" is dropped because $\operatorname{dom} f=\mathbb R^n$.
-- source:
--   Badenbroek & de Klerk, Complexity Analysis of a Sampling-Based Interior Point Method for Convex Optimization, arXiv:1811.07677v1, p. 3, display (4) (Definition 2.1 applied to f, self-concordant by Bubeck–Eldan)

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_ExpFamily
import Definitions.Def_SamplingIPM_Spectra_Model

open scoped RealInnerProductSpace
open EntropicBarrier.Universal

namespace SamplingIPM.Spectra

theorem display_4 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsConvexBody K)
    (θ₀ θ₁ : EuclideanSpace ℝ (Fin n)) (hclose : localNorm K θ₀ (θ₁ - θ₀) < 1)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    (1 - localNorm K θ₀ (θ₁ - θ₀)) * localNorm K θ₀ v ≤ localNorm K θ₁ v ∧
      localNorm K θ₁ v ≤ localNorm K θ₀ v / (1 - localNorm K θ₀ (θ₁ - θ₀)) := by sorry

end SamplingIPM.Spectra
