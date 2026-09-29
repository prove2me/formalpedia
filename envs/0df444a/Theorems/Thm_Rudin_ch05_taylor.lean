-- Prove2me | Theorems.Thm_Rudin_ch05_taylor
-- name    : Rudin.ch05_taylor
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-12T23:15:23.795505+00:00
-- url     : https://prove2.me/theorems/a9b4a179-fc04-469b-a9a4-7bdb07d21b13
-- title:
--   Theorem 5.15 — Taylor's theorem
-- statement:
--   Let $f$ be a real function on $[a,b]$, $n$ a positive integer, $f^{(n-1)}$ continuous on $[a,b]$, and $f^{(n)}(t)$ existing for every $t \in (a,b)$. Let $\alpha \ne \beta$ be points of $[a,b]$ and let $P$ be the Taylor polynomial of $f$ at $\alpha$ of degree $n-1$. Then there is a point $x$ strictly between $\alpha$ and $\beta$ with $$f(\beta) = P(\beta) + \frac{f^{(n)}(x)}{n!}(\beta - \alpha)^n .$$ For $n = 1$ this is the mean value theorem.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 5, pp. 110-111, Definition 5.14 and Theorem 5.15

import Mathlib

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 5.15 (Taylor's theorem): suppose `f` is a real function on `[a, b]`, `n` is
a positive integer, `f^(n-1)` is continuous on `[a, b]` and `f^(n)(t)` exists for every
`t ∈ (a, b)`.  Let `α` and `β` be distinct points of `[a, b]` and let `P` be the Taylor
polynomial of degree `n - 1` of `f` at `α`.  Then there is a point `x` strictly between `α`
and `β` with `f β = P β + f^(n)(x) (β - α)^n / n!`. -/
theorem ch05_taylor (a b : ℝ) (hab : a < b) (f : ℝ → ℝ) (n : ℕ) (hn : 0 < n)
    (hcont : ContinuousOn (iteratedDeriv (n - 1) f) (Set.Icc a b))
    (hderiv : ∀ t ∈ Set.Ioo a b, DifferentiableAt ℝ (iteratedDeriv (n - 1) f) t)
    (α β : ℝ) (hα : α ∈ Set.Icc a b) (hβ : β ∈ Set.Icc a b) (hne : α ≠ β) :
    ∃ x : ℝ, ((α < x ∧ x < β) ∨ (β < x ∧ x < α)) ∧
      f β = (∑ k ∈ Finset.range n, iteratedDeriv k f α / (k.factorial : ℝ) * (β - α) ^ k)
        + iteratedDeriv n f x / (n.factorial : ℝ) * (β - α) ^ n := by sorry

end Rudin
