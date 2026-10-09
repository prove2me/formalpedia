-- Prove2me | Theorems.Thm_RelSmoothFOM_PrimalGrad_eq_28
-- name    : RelSmoothFOM.PrimalGrad.eq_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:36:56.189692+00:00
-- url     : https://prove2.me/theorems/6c067899-e9ac-4b88-8ed8-dbc310da6b07
-- title:
--   (28), pp. 345–346 — one step: f(xⁱ) ≤ f(x) + (L−μ)D_h(x,xⁱ⁻¹) − LD_h(x,xⁱ) via a three-line chain
-- statement:
--   Let $Q$ be a convex subset of a finite-dimensional real inner-product space $E$, and let $f,h:E\to\mathbb R$ be differentiable at every point of $Q$ and convex on $Q$. Let $L>0$ and $\mu\ge0$, and suppose $f$ is $L$-smooth and $\mu$-strongly convex relative to $h$ on $Q$. Let $x^0,x^1,\dots$ be a run of the primal gradient scheme (Algorithm 1) with parameter $L$. Then for every $x\in Q$ and every $i\ge1$,
--
--   $$\begin{aligned}
--   f(x^i)&\le f(x^{i-1})+\langle\nabla f(x^{i-1}),x^i-x^{i-1}\rangle+L D_h(x^i,x^{i-1})\\
--   &\le f(x^{i-1})+\langle\nabla f(x^{i-1}),x-x^{i-1}\rangle+L D_h(x,x^{i-1})-L D_h(x,x^i)\\
--   &\le f(x)+(L-\mu)D_h(x,x^{i-1})-L D_h(x,x^i).
--   \end{aligned}$$
--
--   This one-step inequality is the core of the convergence analysis of the primal gradient scheme: weighted and summed over $i$, it yields the sublinear and linear rates of Theorem 3.1.
--
--   **Formalization Note** The three inequalities are stated separately, as a conjunction. Indices are natural numbers with $i\ge1$, so $i-1$ is the ordinary predecessor. Relative smoothness and strong convexity are assumed on the (relative) interior of $Q$ as in Definitions 1.1–1.2, while the conclusion is for all points and iterates of $Q$.
-- source:
--   Lu, Freund & Nesterov, Relatively smooth convex optimization by first-order methods, and applications, SIAM J. Optim. 28 (2018), pp. 345–346, proof of Theorem 3.1, (28)

import Mathlib
import Definitions.Def_RelSmoothFOM_PrimalGrad_Setting

namespace RelSmoothFOM.PrimalGrad

theorem eq_28 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQ : Convex ℝ Q)
    (f h : E → ℝ) (hfd : ∀ x ∈ Q, DifferentiableAt ℝ f x) (hfc : ConvexOn ℝ Q f)
    (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x) (hhc : ConvexOn ℝ Q h)
    (L μ : ℝ) (hL : 0 < L) (hμ : 0 ≤ μ)
    (hsm : IsRelSmooth Q f h L) (hsc : IsRelStronglyConvex Q f h μ)
    (x : ℕ → E) (hrun : IsPrimalGradientRun Q f h L x) :
    ∀ u ∈ Q, ∀ i : ℕ, 1 ≤ i →
      f (x i) ≤ f (x (i - 1)) + fderiv ℝ f (x (i - 1)) (x i - x (i - 1))
          + L * bregman h (x i) (x (i - 1)) ∧
      f (x (i - 1)) + fderiv ℝ f (x (i - 1)) (x i - x (i - 1))
          + L * bregman h (x i) (x (i - 1))
        ≤ f (x (i - 1)) + fderiv ℝ f (x (i - 1)) (u - x (i - 1))
          + L * bregman h u (x (i - 1)) - L * bregman h u (x i) ∧
      f (x (i - 1)) + fderiv ℝ f (x (i - 1)) (u - x (i - 1))
          + L * bregman h u (x (i - 1)) - L * bregman h u (x i)
        ≤ f u + (L - μ) * bregman h u (x (i - 1)) - L * bregman h u (x i) := by sorry

end RelSmoothFOM.PrimalGrad
