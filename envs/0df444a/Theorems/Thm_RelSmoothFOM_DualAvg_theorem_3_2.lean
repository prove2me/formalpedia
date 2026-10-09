-- Prove2me | Theorems.Thm_RelSmoothFOM_DualAvg_theorem_3_2
-- name    : RelSmoothFOM.DualAvg.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:34:34.608975+00:00
-- url     : https://prove2.me/theorems/e45d32d6-e3ad-4bea-bca5-8c1d9d423c42
-- title:
--   Theorem 3.2, p. 347 — dual averaging scheme: min_{i≤k} f(x^i) − f(x) ≤ μh(x)/((1+μ/(L−μ))^k − 1) ≤ (L−μ)h(x)/k
-- statement:
--   Let $Q$ be a convex subset of a finite-dimensional real inner-product space $E$, and let $f, h : E \to \mathbb R$ be convex on $Q$ and differentiable at every point of $Q$; $h$ is the reference function. Let $0 \le \mu < L$ and suppose $f$ is $L$-smooth and $\mu$-strongly convex relative to $h$ on $Q$ (Definitions 1.1 and 1.2). Let $(x^k)_{k \ge 0}$ be a run of the dual averaging scheme (Algorithm 2): $x^0$ minimises $h$ over $Q$ with $h(x^0) = 0$, and for $k \ge 0$
--   $$x^{k+1} \in \arg\min_{x \in Q}\Big\{h(x) + \sum_{i=0}^{k} a_{i+1}\big(f(x^i) + \langle \nabla f(x^i), x - x^i\rangle + \mu D_h(x, x^i)\big)\Big\}, \qquad a_{i+1} = \frac{1}{L-\mu}\Big(\frac{L}{L-\mu}\Big)^i .$$
--   Then for every $k \ge 1$ and every $x \in Q$,
--   $$\min_{i=1,\dots,k} f(x^i) - f(x) \le \frac{\mu h(x)}{\left(1 + \frac{\mu}{L-\mu}\right)^k - 1} \le \frac{L-\mu}{k}\, h(x),$$
--   where for $\mu = 0$ the middle expression is understood as its limit as $\mu \to 0^+$, which is the right-hand side.
--
--   With $\mu > 0$ the middle bound decays geometrically, so the dual averaging scheme converges linearly under relative strong convexity; with $\mu = 0$ it attains the $O(1/k)$ rate of the primal gradient scheme, without any strong convexity of $h$.
--
--   **Formalization Note** The statement is split into two parts: (i) for every $0 \le \mu < L$, some $i \in \{1,\dots,k\}$ has $f(x^i) - f(x) \le \frac{L-\mu}{k} h(x)$; (ii) if $\mu > 0$, some $i \in \{1,\dots,k\}$ satisfies the middle bound, and the middle bound is at most the right-hand side. The limit at $\mu = 0$ is not formalised; part (i) is what it asserts. The minimum over $i$ is written as an existential, which is equivalent. The page's "$L > \mu$" with $\mu \ge 0$ is the pair of hypotheses $0 \le \mu < L$. Definitions 1.1–1.2 are required only on the (relative) interior of $Q$, as on the page, while the conclusion is for every $x \in Q$, as on the page; iterates may lie on the relative boundary. The page's closedness of $Q$ is not assumed, which makes the statement stronger.
-- source:
--   Lu, Freund & Nesterov, Relatively smooth convex optimization by first-order methods, and applications, SIAM J. Optim. 28 (2018), p. 347, Theorem 3.2 and (32); Algorithm 2, p. 346

import Mathlib
import Definitions.Def_RelSmoothFOM_DualAvg_Setting

namespace RelSmoothFOM.DualAvg

/-- Theorem 3.2, p. 347: for the dual averaging scheme (Algorithm 2), if `f` is `L`-smooth and
`μ`-strongly convex relative to `h` with `L > μ ≥ 0`, then for all `k ≥ 1` and `u ∈ Q`,
`min_{i=1,…,k} f(x^i) − f(u) ≤ μh(u)/((1 + μ/(L − μ))^k − 1) ≤ ((L − μ)/k) h(u)`.
The case `μ = 0` (middle term defined as a limit) is carried by the outer bound, stated for
every `0 ≤ μ < L`. -/
theorem theorem_3_2
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQ : Convex ℝ Q)
    (f h : E → ℝ) (hfd : ∀ x ∈ Q, DifferentiableAt ℝ f x) (hfc : ConvexOn ℝ Q f)
    (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x) (hhc : ConvexOn ℝ Q h)
    (L μ : ℝ) (hμ : 0 ≤ μ) (hμL : μ < L)
    (hsm : IsRelSmooth Q f h L) (hsc : IsRelStronglyConvex Q f h μ)
    (x : ℕ → E) (hrun : IsDualAveragingRun Q f h L μ x) :
    ∀ k : ℕ, 1 ≤ k → ∀ u ∈ Q,
      (∃ i ∈ Finset.Icc 1 k, f (x i) - f u ≤ (L - μ) / k * h u) ∧
      (0 < μ →
        (∃ i ∈ Finset.Icc 1 k, f (x i) - f u ≤ μ * h u / ((1 + μ / (L - μ)) ^ k - 1)) ∧
        μ * h u / ((1 + μ / (L - μ)) ^ k - 1) ≤ (L - μ) / k * h u) := by sorry

end RelSmoothFOM.DualAvg
