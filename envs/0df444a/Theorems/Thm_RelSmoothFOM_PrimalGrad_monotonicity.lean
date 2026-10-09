-- Prove2me | Theorems.Thm_RelSmoothFOM_PrimalGrad_monotonicity
-- name    : RelSmoothFOM.PrimalGrad.monotonicity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:34:33.332882+00:00
-- url     : https://prove2.me/theorems/27a4e5f6-a11b-4a78-a110-ed871f620043
-- title:
--   Proof of Theorem 3.1, p. 346 — the primal gradient scheme is monotone: f(xⁱ⁺¹) ≤ f(xⁱ)
-- statement:
--   Let $Q$ be a convex subset of a finite-dimensional real inner-product space $E$, and let $f,h:E\to\mathbb R$ be differentiable at every point of $Q$ and convex on $Q$. Let $L>0$ and suppose $f$ is $L$-smooth relative to $h$ on $Q$. If $x^0,x^1,\dots$ is a run of the primal gradient scheme (Algorithm 1) with parameter $L$, then the objective values are nonincreasing:
--
--   $$f(x^{i+1})\le f(x^i)\qquad\text{for all } i\ge0.$$
--
--   Monotonicity is used in the proof of Theorem 3.1 to replace the weighted average of $f(x^1),\dots,f(x^k)$ by the last value $f(x^k)$.
--
--   **Formalization Note** The paper derives monotonicity inside the proof of Theorem 3.1, under all of that theorem's hypotheses, by substituting $x=x^{i-1}$ in (28). The statement here drops the relative strong convexity hypothesis, which the argument does not use; this makes it a stronger statement. Iterates are indexed from $0$, so the claim $f(x^i)\le f(x^{i-1})$ for $i\ge1$ is written $f(x^{i+1})\le f(x^i)$ for $i\ge0$.
-- source:
--   Lu, Freund & Nesterov, Relatively smooth convex optimization by first-order methods, and applications, SIAM J. Optim. 28 (2018), p. 346, proof of Theorem 3.1, monotonicity

import Mathlib
import Definitions.Def_RelSmoothFOM_PrimalGrad_Setting

namespace RelSmoothFOM.PrimalGrad

theorem monotonicity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQ : Convex ℝ Q)
    (f h : E → ℝ) (hfd : ∀ x ∈ Q, DifferentiableAt ℝ f x) (hfc : ConvexOn ℝ Q f)
    (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x) (hhc : ConvexOn ℝ Q h)
    (L : ℝ) (hL : 0 < L) (hsm : IsRelSmooth Q f h L)
    (x : ℕ → E) (hrun : IsPrimalGradientRun Q f h L x) :
    ∀ i : ℕ, f (x (i + 1)) ≤ f (x i) := by sorry

end RelSmoothFOM.PrimalGrad
