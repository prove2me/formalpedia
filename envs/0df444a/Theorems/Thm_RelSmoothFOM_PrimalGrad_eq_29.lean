-- Prove2me | Theorems.Thm_RelSmoothFOM_PrimalGrad_eq_29
-- name    : RelSmoothFOM.PrimalGrad.eq_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:34:31.267926+00:00
-- url     : https://prove2.me/theorems/1e28d160-dc9e-408f-a79a-1d802a15aebd
-- title:
--   (29), p. 346 — Σᵢ (L/(L−μ))ⁱ f(xⁱ) ≤ Σᵢ (L/(L−μ))ⁱ f(x) + LD_h(x,x⁰) − (L/(L−μ))ᵏ LD_h(x,xᵏ)
-- statement:
--   Let $Q$ be a convex subset of a finite-dimensional real inner-product space $E$, and let $f,h:E\to\mathbb R$ be differentiable at every point of $Q$ and convex on $Q$. Let $0\le\mu<L$, and suppose $f$ is $L$-smooth and $\mu$-strongly convex relative to $h$ on $Q$. Let $x^0,x^1,\dots$ be a run of the primal gradient scheme (Algorithm 1) with parameter $L$. Then for every $k\ge1$ and every $x\in Q$,
--
--   $$\sum_{i=1}^k\Big(\frac{L}{L-\mu}\Big)^i f(x^i)\;\le\;\sum_{i=1}^k\Big(\frac{L}{L-\mu}\Big)^i f(x)+L D_h(x,x^0)-\Big(\frac{L}{L-\mu}\Big)^k L D_h(x,x^k).$$
--
--   This weighted sum of the one-step inequalities (28) telescopes the Bregman terms; together with monotonicity it gives the rate of Theorem 3.1.
--
--   **Formalization Note** The paper's Theorem 3.1 says "$L>0$ and $\mu\ge0$"; the hypothesis $\mu<L$ is added because the weights divide by $L-\mu$ (at $\mu=L$ the expression is undefined on the page, while Lean's convention $a/0=0$ would silently change the claim). $L>0$ is kept as stated on the page.
-- source:
--   Lu, Freund & Nesterov, Relatively smooth convex optimization by first-order methods, and applications, SIAM J. Optim. 28 (2018), p. 346, proof of Theorem 3.1, (29)

import Mathlib
import Definitions.Def_RelSmoothFOM_PrimalGrad_Setting

namespace RelSmoothFOM.PrimalGrad

theorem eq_29 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQ : Convex ℝ Q)
    (f h : E → ℝ) (hfd : ∀ x ∈ Q, DifferentiableAt ℝ f x) (hfc : ConvexOn ℝ Q f)
    (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x) (hhc : ConvexOn ℝ Q h)
    (L μ : ℝ) (hL : 0 < L) (hμ : 0 ≤ μ) (hμL : μ < L)
    (hsm : IsRelSmooth Q f h L) (hsc : IsRelStronglyConvex Q f h μ)
    (x : ℕ → E) (hrun : IsPrimalGradientRun Q f h L x) :
    ∀ k : ℕ, 1 ≤ k → ∀ u ∈ Q,
      ∑ i ∈ Finset.Icc 1 k, (L / (L - μ)) ^ i * f (x i)
        ≤ ∑ i ∈ Finset.Icc 1 k, (L / (L - μ)) ^ i * f u + L * bregman h u (x 0)
          - (L / (L - μ)) ^ k * (L * bregman h u (x k)) := by sorry

end RelSmoothFOM.PrimalGrad
