-- Prove2me | Theorems.Thm_SubspaceProxGrad_RPSD_theorem_1
-- name    : SubspaceProxGrad.RPSD.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:18:57.892135+00:00
-- url     : https://prove2.me/theorems/6a5e96f1-d211-4127-a846-c869969cc237
-- title:
--   Theorem 1, p. 5 — RPSD: 𝔼‖x^{k+1} − x⋆‖² ≤ (1 − λmin(P)·2γμL/(μ+L))^k·C and x^k → x⋆ almost surely
-- statement:
--   Consider the composite problem (1),
--   $$\min_{x\in\mathbb R^n}\ f(x)+g(x),$$
--   where $f$ is $L$-smooth (differentiable with $L$-Lipschitz gradient) and $\mu$-strongly convex, $0<\mu$, $0<L$, and $g:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ is convex, proper and lower semicontinuous (Assumption 1); let $x^\star$ be its unique minimizer. Let $\mathfrak S^1,\mathfrak S^2,\dots$ be an i.i.d. sequence of admissible random subspaces (Assumption 2), with average projection $\mathsf P=\mathbb E[P_{\mathfrak S^1}]$, and let $\mathsf Q=\mathsf P^{-1/2}$. Fix a step size
--   $$\gamma\in\Big(0,\frac{2}{\mu+L}\Big],$$
--   and a starting point $z^0$. Then the iterates $(x^k)$ of the randomized proximal subspace descent (RPSD, Algorithm 1) converge almost surely to $x^\star$, with rate
--   $$\mathbb E\big[\|x^{k+1}-x^\star\|_2^2\big]\le\Big(1-\lambda_{\min}(\mathsf P)\frac{2\gamma\mu L}{\mu+L}\Big)^k C\qquad(k\ge0),$$
--   where $C=\lambda_{\max}(\mathsf P)\,\|z^0-\mathsf Q(x^\star-\gamma\nabla f(x^\star))\|_2^2$.
--
--   This is the main convergence result for RPSD: a proximal gradient method whose gradient step is applied only along a random subspace, corrected by the change of basis $\mathsf Q$, converges linearly in expectation at a rate governed by the smallest eigenvalue of the average projection, for the usual step-size range of proximal gradient descent and without separability of $g$.
--
--   **Formalization Note.** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`. The selections are $\mathfrak S^{k+1}=\mathrm{sel}(\xi_k)$ with $(\xi_k)$ i.i.d. random variables in a measurable space $\Theta$ and $\theta\mapsto P_{\mathrm{sel}(\theta)}x$ measurable (this keeps the integral defining $\mathsf P$ the true expectation). $\mathsf Q=\mathsf P^{-1/2}$ is encoded as a positive self-adjoint map with $\mathsf Q\mathsf P\mathsf Q=I$ and a two-sided inverse $\mathsf Q^{-1}$; these characterize the positive square root of $\mathsf P^{-1}$. $g$ is the pair $(\operatorname{dom}g, g)$: proper is a nonempty domain, lower semicontinuity is a closed epigraph. $\mu$-strong convexity is Mathlib's `StrongConvexOn` with modulus $\mu$. The minimizer and the run are universally quantified. Both conclusions are stated: the rate for every $k\ge0$ (the case $k=0$ reads $\mathbb E\|x^1-x^\star\|^2\le C$) as a Bochner integral, and almost-sure convergence $x^k\to x^\star$.
-- source:
--   Grishchenko, Iutzeler & Malick, Proximal gradient methods with adaptive subspace sampling, arXiv:2004.13356v1, p. 5, Theorem 1

import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic
import Definitions.Def_SubspaceProxGrad_RPSD_Setting

open MeasureTheory ProbabilityTheory

namespace SubspaceProxGrad.RPSD

theorem theorem_1 {n : ℕ} {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    (pr : Measure Ω) [IsProbabilityMeasure pr]
    (sel : Θ → Submodule ℝ (E n)) (hsel : ∀ x : E n, Measurable fun θ => (sel θ).starProjection x)
    (ξ : ℕ → Ω → Θ) (hξ : ∀ k, Measurable (ξ k)) (hind : iIndepFun ξ pr)
    (hid : ∀ k, IdentDistrib (ξ k) (ξ 0) pr pr)
    (hadm : IsAdmissible pr (fun ω => sel (ξ 0 ω)))
    (P : E n →L[ℝ] E n) (hP : IsAvgProj pr (fun ω => sel (ξ 0 ω)) P)
    (Q Qinv : E n →L[ℝ] E n) (hQ : Q.IsPositive)
    (hQPQ : Q ∘L P ∘L Q = ContinuousLinearMap.id ℝ (E n))
    (hQi : Q ∘L Qinv = ContinuousLinearMap.id ℝ (E n))
    (hQi' : Qinv ∘L Q = ContinuousLinearMap.id ℝ (E n))
    (f : E n → ℝ) (μ L : ℝ) (hμ : 0 < μ) (hL : 0 < L) (hfd : Differentiable ℝ f)
    (hfs : StrongConvexOn Set.univ μ f)
    (hfL : ∀ x y : E n, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (C : Set (E n)) (g : E n → ℝ) (hC : C.Nonempty) (hg : ConvexOn ℝ C g)
    (hgl : IsClosed {p : E n × ℝ | p.1 ∈ C ∧ g p.1 ≤ p.2})
    (xs : E n) (hxs : IsMinimizer C f g xs)
    (γ : ℝ) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 2 / (μ + L))
    (z0 : E n) (z x : ℕ → Ω → E n) (hrun : IsRPSDRun sel ξ C f g γ Q Qinv z0 z x) :
    (∀ k : ℕ, ∫ ω, ‖x (k + 1) ω - xs‖ ^ 2 ∂pr ≤
      (1 - lamMin P * (2 * γ * μ * L / (μ + L))) ^ k *
        (lamMax P * ‖z0 - Q (xs - γ • gradient f xs)‖ ^ 2)) ∧
    (∀ᵐ ω ∂pr, Filter.Tendsto (fun k => x k ω) Filter.atTop (nhds xs)) := by sorry

end SubspaceProxGrad.RPSD
