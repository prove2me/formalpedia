-- Prove2me | Theorems.Thm_RelSmoothFOM_PrimalGrad_theorem_3_1
-- name    : RelSmoothFOM.PrimalGrad.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:34:37.567583+00:00
-- url     : https://prove2.me/theorems/edda1c61-fade-4d9b-ac3e-fab885e01169
-- title:
--   Theorem 3.1, p. 344 — primal gradient scheme: f(xᵏ) nonincreasing and f(xᵏ) − f(x) ≤ μD_h(x,x⁰)/((1+μ/(L−μ))ᵏ − 1) ≤ (L−μ)D_h(x,x⁰)/k
-- statement:
--   Let $Q$ be a convex subset of a finite-dimensional real inner-product space $E$, and let $f,h:E\to\mathbb R$ be differentiable at every point of $Q$ and convex on $Q$; $h$ is the reference function and $D_h(y,x)=h(y)-h(x)-\langle\nabla h(x),y-x\rangle$ its Bregman distance. Let $L>0$ and $0\le\mu<L$, and suppose $f$ is $L$-smooth and $\mu$-strongly convex relative to $h$ on $Q$. Let $x^0,x^1,\dots$ be a run of the primal gradient scheme (Algorithm 1) with parameter $L$. Then:
--
--   1. the sequence $f(x^k)$ is nonincreasing;
--   2. for all $k\ge1$ and $x\in Q$,
--   $$f(x^k)-f(x)\;\le\;\frac{L-\mu}{k}\,D_h(x,x^0);$$
--   3. if moreover $\mu>0$, then for all $k\ge1$ and $x\in Q$,
--   $$f(x^k)-f(x)\;\le\;\frac{\mu\,D_h(x,x^0)}{\big(1+\frac{\mu}{L-\mu}\big)^k-1}\;\le\;\frac{L-\mu}{k}\,D_h(x,x^0).$$
--
--   The theorem gives an $O(1/k)$ rate for the primal gradient scheme whenever $f$ is smooth relative to $h$, and a linear rate when $f$ is also strongly convex relative to $h$, without any Lipschitz gradient or strong convexity in the usual sense and without strong convexity of $h$.
--
--   **Formalization Note** The paper states (26) as a single chain for all $\mu\ge0$, with the middle term "defined in the limit as $\mu\to0^+$"; that limit equals the right-hand term, so the statement here gives the right-hand bound for every $0\le\mu<L$ and the full chain for $\mu>0$, and no limit is formalized. The hypothesis $\mu<L$ is added: (26) divides by $L-\mu$, and at $\mu=L$ the page's expression is undefined while Lean's $a/0=0$ would change its meaning. "Monotonically decreasing" is read as nonincreasing, which is what the proof gives. Relative smoothness and strong convexity are assumed on the (relative) interior of $Q$ (Definitions 1.1–1.2), while the conclusion holds for every $x\in Q$ and the iterates may lie anywhere in $Q$. Closedness of $Q$ is not assumed (no step of the argument uses it), which makes the statement stronger. Differentiability of $f,h$ is differentiability as functions on $E$ at each point of $Q$.
-- source:
--   Lu, Freund & Nesterov, Relatively smooth convex optimization by first-order methods, and applications, SIAM J. Optim. 28 (2018), p. 344, Theorem 3.1 and (26)

import Mathlib
import Definitions.Def_RelSmoothFOM_PrimalGrad_Setting

namespace RelSmoothFOM.PrimalGrad

theorem theorem_3_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQ : Convex ℝ Q)
    (f h : E → ℝ) (hfd : ∀ x ∈ Q, DifferentiableAt ℝ f x) (hfc : ConvexOn ℝ Q f)
    (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x) (hhc : ConvexOn ℝ Q h)
    (L μ : ℝ) (hL : 0 < L) (hμ : 0 ≤ μ) (hμL : μ < L)
    (hsm : IsRelSmooth Q f h L) (hsc : IsRelStronglyConvex Q f h μ)
    (x : ℕ → E) (hrun : IsPrimalGradientRun Q f h L x) :
    (∀ i : ℕ, f (x (i + 1)) ≤ f (x i)) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ u ∈ Q,
      f (x k) - f u ≤ (L - μ) / (k : ℝ) * bregman h u (x 0)) ∧
    (0 < μ → ∀ k : ℕ, 1 ≤ k → ∀ u ∈ Q,
      f (x k) - f u ≤ μ * bregman h u (x 0) / ((1 + μ / (L - μ)) ^ k - 1) ∧
      μ * bregman h u (x 0) / ((1 + μ / (L - μ)) ^ k - 1)
        ≤ (L - μ) / (k : ℝ) * bregman h u (x 0)) := by sorry

end RelSmoothFOM.PrimalGrad
