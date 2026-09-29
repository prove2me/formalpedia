-- Prove2me | Theorems.Thm_Rudin_ch05_taylor_of_differentiable
-- name    : Rudin.ch05_taylor_of_differentiable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-14T05:18:55.635968+00:00
-- url     : https://prove2.me/theorems/13a86130-2859-4fd1-b33f-239a8173e1aa
-- title:
--   Taylor's theorem with Lagrange remainder (Rudin 5.15), corrected
-- statement:
--   **Taylor's theorem with Lagrange remainder.** Let $f$ be a real function on $[a,b]$ and let $n \ge 1$. Suppose that for every $k < n-1$ the $k$-th derivative $f^{(k)}$ exists as a genuine derivative at each point of $[a,b]$, that $f^{(n-1)}$ is continuous on $[a,b]$, and that $f^{(n)}(t)$ exists for every $t \in (a,b)$. Let $\alpha \neq \beta$ be points of $[a,b]$ and let
--   $$P(t) \;=\; \sum_{k=0}^{n-1} \frac{f^{(k)}(\alpha)}{k!}\,(t-\alpha)^k$$
--   be the Taylor polynomial of degree $n-1$ of $f$ at $\alpha$. Then there is a point $x$ strictly between $\alpha$ and $\beta$ with
--   $$f(\beta) \;=\; P(\beta) + \frac{f^{(n)}(x)}{n!}\,(\beta-\alpha)^n.$$
--
--   For $n = 1$ this is the mean value theorem; in general it measures how well the Taylor polynomial approximates $f$ near $\alpha$.
--
--   **Formalization note.** The explicit hypothesis on the lower derivatives is what makes the statement faithful. Lean's `deriv` is a total function that returns $0$ wherever a function fails to be differentiable, so an iterated-derivative hypothesis stated only at level $n-1$ constrains nothing below it. For instance, with $n = 2$ and $f$ the indicator function of the rationals, $\operatorname{deriv} f$ is identically $0$ — hence continuous and differentiable — and the conclusion would degenerate to $f(\beta) = f(\alpha)$ for all $\alpha \neq \beta$, which is false. Requiring $f^{(k)}$ to be genuinely differentiable on $[a,b]$ for $k < n-1$ is exactly Rudin's standing assumption that the derivatives up to order $n-1$ exist.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd ed., Chapter 5, Theorem 5.15, p. 110. Corrected form of the platform theorem Rudin.ch05_taylor (disproved).

import Mathlib

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 5.15 (Taylor's theorem), with the hypothesis that the lower derivatives are
genuine derivatives on `[a, b]`. -/
theorem ch05_taylor_of_differentiable (a b : ℝ) (hab : a < b) (f : ℝ → ℝ) (n : ℕ) (hn : 0 < n)
    (hlower : ∀ k < n - 1, ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (iteratedDeriv k f) t)
    (hcont : ContinuousOn (iteratedDeriv (n - 1) f) (Set.Icc a b))
    (hderiv : ∀ t ∈ Set.Ioo a b, DifferentiableAt ℝ (iteratedDeriv (n - 1) f) t)
    (α β : ℝ) (hα : α ∈ Set.Icc a b) (hβ : β ∈ Set.Icc a b) (hne : α ≠ β) :
    ∃ x : ℝ, ((α < x ∧ x < β) ∨ (β < x ∧ x < α)) ∧
      f β = (∑ k ∈ Finset.range n, iteratedDeriv k f α / (k.factorial : ℝ) * (β - α) ^ k)
        + iteratedDeriv n f x / (n.factorial : ℝ) * (β - α) ^ n := by sorry

end Rudin
