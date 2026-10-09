-- Prove2me | Theorems.Thm_RelSmoothFOM_PrimalGrad_eq_31
-- name    : RelSmoothFOM.PrimalGrad.eq_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:34:44.396409+00:00
-- url     : https://prove2.me/theorems/8fb4fd43-53c5-4d12-a62d-8351ba0ea59e
-- title:
--   (31), p. 346 — f(xᵏ) − f(x) ≤ C_k LD_h(x,x⁰) = μD_h(x,x⁰)/((1+μ/(L−μ))ᵏ − 1) for μ > 0
-- statement:
--   Let $Q$ be a convex subset of a finite-dimensional real inner-product space $E$, and let $f,h:E\to\mathbb R$ be differentiable at every point of $Q$ and convex on $Q$. Let $0<\mu<L$, and suppose $f$ is $L$-smooth and $\mu$-strongly convex relative to $h$ on $Q$. Let $x^0,x^1,\dots$ be a run of the primal gradient scheme (Algorithm 1) with parameter $L$, and let $C_k=1\big/\sum_{i=1}^k\big(\frac{L}{L-\mu}\big)^i$. Then for every $k\ge1$ and every $x\in Q$,
--
--   $$f(x^k)-f(x)\;\le\;C_k\,L\,D_h(x,x^0)\;=\;\frac{\mu D_h(x,x^0)}{\big(1+\frac{\mu}{L-\mu}\big)^k-1}.$$
--
--   This is the first inequality of (26) in Theorem 3.1, the linear convergence rate of the primal gradient scheme under relative strong convexity.
--
--   **Formalization Note** The inequality and the equality are stated separately, as a conjunction. The closed form of $C_k$ holds only for $\mu>0$ (the case $\mu=0$ is covered by the right-hand bound of Theorem 3.1), so this item assumes $0<\mu$. The hypothesis $\mu<L$ is added because the formula divides by $L-\mu$.
-- source:
--   Lu, Freund & Nesterov, Relatively smooth convex optimization by first-order methods, and applications, SIAM J. Optim. 28 (2018), p. 346, proof of Theorem 3.1, (31)

import Mathlib
import Definitions.Def_RelSmoothFOM_PrimalGrad_Setting

namespace RelSmoothFOM.PrimalGrad

theorem eq_31 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQ : Convex ℝ Q)
    (f h : E → ℝ) (hfd : ∀ x ∈ Q, DifferentiableAt ℝ f x) (hfc : ConvexOn ℝ Q f)
    (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x) (hhc : ConvexOn ℝ Q h)
    (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ) (hμL : μ < L)
    (hsm : IsRelSmooth Q f h L) (hsc : IsRelStronglyConvex Q f h μ)
    (x : ℕ → E) (hrun : IsPrimalGradientRun Q f h L x) :
    ∀ k : ℕ, 1 ≤ k → ∀ u ∈ Q,
      f (x k) - f u
          ≤ (1 / ∑ i ∈ Finset.Icc 1 k, (L / (L - μ)) ^ i) * (L * bregman h u (x 0)) ∧
      (1 / ∑ i ∈ Finset.Icc 1 k, (L / (L - μ)) ^ i) * (L * bregman h u (x 0))
          = μ * bregman h u (x 0) / ((1 + μ / (L - μ)) ^ k - 1) := by sorry

end RelSmoothFOM.PrimalGrad
