-- Prove2me | Theorems.Thm_Rudin_ch05_taylor_corrected
-- name    : Rudin.ch05_taylor_corrected
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T03:54:45.602692+00:00
-- url     : https://prove2.me/theorems/61652ac9-3718-44d2-ae64-a03d1ec3c534
-- title:
--   Theorem 5.15 — Taylor's theorem (hypotheses on all orders)
-- statement:
--   Let $f$ be a real function on $[a,b]$, let $n \ge 1$, and suppose that for every $k \le n-1$
--
--   $$f^{(k)} \text{ is continuous on } [a,b], \qquad f^{(k+1)}(t) \text{ exists for every } t \in (a,b).$$
--
--   Let $\alpha \ne \beta$ be points of $[a,b]$ and let
--
--   $$P(t) = \sum_{k=0}^{n-1} \frac{f^{(k)}(\alpha)}{k!}\,(t-\alpha)^{k}$$
--
--   be the Taylor polynomial of $f$ at $\alpha$ of degree $n-1$. Then there is a point $x$ strictly between $\alpha$ and $\beta$ with
--
--   $$f(\beta) = P(\beta) + \frac{f^{(n)}(x)}{n!}\,(\beta-\alpha)^{n}.$$
--
--   For $n = 1$ this is the mean value theorem.
--
--   This is Theorem 5.15 of Rudin's *Principles of Mathematical Analysis*. Rudin states the hypotheses only for the top order ("$f^{(n-1)}$ is continuous on $[a,b]$ and $f^{(n)}(t)$ exists for $t \in (a,b)$"), the existence and continuity of the lower-order derivatives being implicit in his convention that $f^{(n)}$ exists on a set only if $f^{(n-1)}$ exists in a neighbourhood of each of its points. In Lean, `iteratedDeriv k f` is a total function that takes the junk value $0$ wherever the derivative fails to exist, so a hypothesis on the single order $n-1$ carries no information about $f$ itself; the hypotheses above are therefore quantified over all orders $k \le n-1$, which is the faithful reading of Rudin's statement.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 5, pp. 110-111, Definition 5.14 and Theorem 5.15

import Mathlib

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 5.15 (Taylor's theorem), with the differentiability hypotheses stated for
every order `k ≤ n - 1`: if `f, f', …, f^(n-1)` are continuous on `[a, b]` and `f^(k+1)(t)`
exists for every `t ∈ (a, b)` and every `k ≤ n - 1`, and `α ≠ β` are points of `[a, b]`, then
there is a point `x` strictly between `α` and `β` with
`f β = ∑_{k<n} f^(k)(α)/k! (β-α)^k + f^(n)(x)/n! (β-α)^n`. -/
theorem ch05_taylor_corrected (a b : ℝ) (hab : a < b) (f : ℝ → ℝ) (n : ℕ) (hn : 0 < n)
    (hcont : ∀ k ≤ n - 1, ContinuousOn (iteratedDeriv k f) (Set.Icc a b))
    (hderiv : ∀ k ≤ n - 1, ∀ t ∈ Set.Ioo a b, DifferentiableAt ℝ (iteratedDeriv k f) t)
    (α β : ℝ) (hα : α ∈ Set.Icc a b) (hβ : β ∈ Set.Icc a b) (hne : α ≠ β) :
    ∃ x : ℝ, ((α < x ∧ x < β) ∨ (β < x ∧ x < α)) ∧
      f β = (∑ k ∈ Finset.range n, iteratedDeriv k f α / (k.factorial : ℝ) * (β - α) ^ k)
        + iteratedDeriv n f x / (n.factorial : ℝ) * (β - α) ^ n := by sorry

end Rudin
