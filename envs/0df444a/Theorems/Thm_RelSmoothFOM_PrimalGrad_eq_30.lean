-- Prove2me | Theorems.Thm_RelSmoothFOM_PrimalGrad_eq_30
-- name    : RelSmoothFOM.PrimalGrad.eq_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:36:54.240299+00:00
-- url     : https://prove2.me/theorems/9f3cbcdc-75c6-47c8-8dde-c082ea3d369f
-- title:
--   (30), p. 346 — (Σᵢ (L/(L−μ))ⁱ)(f(xᵏ) − f(x)) ≤ LD_h(x,x⁰) − (L/(L−μ))ᵏ LD_h(x,xᵏ) ≤ LD_h(x,x⁰)
-- statement:
--   Let $Q$ be a convex subset of a finite-dimensional real inner-product space $E$, and let $f,h:E\to\mathbb R$ be differentiable at every point of $Q$ and convex on $Q$. Let $0\le\mu<L$, and suppose $f$ is $L$-smooth and $\mu$-strongly convex relative to $h$ on $Q$. Let $x^0,x^1,\dots$ be a run of the primal gradient scheme (Algorithm 1) with parameter $L$. Then for every $k\ge1$ and every $x\in Q$,
--
--   $$\Big(\sum_{i=1}^k\Big(\frac{L}{L-\mu}\Big)^i\Big)\big(f(x^k)-f(x)\big)\;\le\;L D_h(x,x^0)-\Big(\frac{L}{L-\mu}\Big)^k L D_h(x,x^k)\;\le\;L D_h(x,x^0).$$
--
--   Dividing by the sum of the weights gives the bound (31) on the optimality gap of the last iterate.
--
--   **Formalization Note** Both inequalities are stated, as a conjunction. The hypothesis $\mu<L$ is added (the weights divide by $L-\mu$); $L>0$ is kept as stated on the page.
-- source:
--   Lu, Freund & Nesterov, Relatively smooth convex optimization by first-order methods, and applications, SIAM J. Optim. 28 (2018), p. 346, proof of Theorem 3.1, (30)

import Mathlib
import Definitions.Def_RelSmoothFOM_PrimalGrad_Setting

namespace RelSmoothFOM.PrimalGrad

theorem eq_30 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQ : Convex ℝ Q)
    (f h : E → ℝ) (hfd : ∀ x ∈ Q, DifferentiableAt ℝ f x) (hfc : ConvexOn ℝ Q f)
    (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x) (hhc : ConvexOn ℝ Q h)
    (L μ : ℝ) (hL : 0 < L) (hμ : 0 ≤ μ) (hμL : μ < L)
    (hsm : IsRelSmooth Q f h L) (hsc : IsRelStronglyConvex Q f h μ)
    (x : ℕ → E) (hrun : IsPrimalGradientRun Q f h L x) :
    ∀ k : ℕ, 1 ≤ k → ∀ u ∈ Q,
      (∑ i ∈ Finset.Icc 1 k, (L / (L - μ)) ^ i) * (f (x k) - f u)
          ≤ L * bregman h u (x 0) - (L / (L - μ)) ^ k * (L * bregman h u (x k)) ∧
      L * bregman h u (x 0) - (L / (L - μ)) ^ k * (L * bregman h u (x k))
          ≤ L * bregman h u (x 0) := by sorry

end RelSmoothFOM.PrimalGrad
