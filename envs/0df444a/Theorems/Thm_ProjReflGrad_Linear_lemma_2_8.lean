-- Prove2me | Theorems.Thm_ProjReflGrad_Linear_lemma_2_8
-- name    : ProjReflGrad.Linear.lemma_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:14:10.57642+00:00
-- url     : https://prove2.me/theorems/f2815763-c181-4b83-a5e2-26d6a14db7f9
-- title:
--   Lemma 2.8, p. 3 — a two-step recursion a_{n+1} + b_{n+1} ≤ (1 − 2α)a_n + αa_{n−1} + βb_n forces a_n ≤ γⁿM
-- statement:
--   Let $(a_n)_{n\ge0}$, $(b_n)_{n\ge0}$ be nonnegative real sequences and $\alpha_0,\beta\in(0,1)$. Suppose that for every $\alpha\in(0,\alpha_0)$ and every $n\ge1$
--   $$a_{n+1}+b_{n+1}\ \le\ (1-2\alpha)a_n+\alpha a_{n-1}+\beta b_n .\qquad(2.1)$$
--   Then there exist $\gamma\in(0,1)$ and $M>0$ such that
--   $$a_n\ \le\ \gamma^n M\qquad\text{for every } n>0 .$$
--
--   This elementary lemma on real sequences turns the two-step recursion (3.9) into the R-linear rate of Theorem 3.3.
--
--   **Formalization Note.** The paper does not state the range of $n$ in (2.1); its proof iterates (2.1) down to $a_1+\delta a_0+b_1$, i.e. uses it for $n\ge1$, and that is the range assumed here. The proof's choice $M=a_1+\delta a_0+b_1$ may be $0$; the conclusion still holds with $M>0$ after enlarging $M$.
-- source:
--   Malitsky, Projected Reflected Gradient Methods for Monotone Variational Inequalities, arXiv:1502.04968v1, p. 3, Lemma 2.8, (2.1)

import Mathlib
import Definitions.Def_ProjReflGrad_Linear_Setting

namespace ProjReflGrad.Linear

/-- Lemma 2.8 (Malitsky 2015, p. 3): let `(a_n)`, `(b_n)` be nonnegative real sequences and
`α₀, β ∈ (0, 1)` such that for every `α ∈ (0, α₀)` and every `n ≥ 1`
`a_{n+1} + b_{n+1} ≤ (1 - 2α)a_n + αa_{n-1} + βb_n` (2.1).
Then there are `γ ∈ (0, 1)` and `M > 0` with `a_n ≤ γⁿM` for every `n > 0`. -/
theorem lemma_2_8 (a b : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) (α0 β : ℝ)
    (hα0 : 0 < α0 ∧ α0 < 1) (hβ : 0 < β ∧ β < 1)
    (h21 : ∀ α : ℝ, 0 < α → α < α0 → ∀ n : ℕ, 1 ≤ n →
      a (n + 1) + b (n + 1) ≤ (1 - 2 * α) * a n + α * a (n - 1) + β * b n) :
    ∃ γ M : ℝ, 0 < γ ∧ γ < 1 ∧ 0 < M ∧ ∀ n : ℕ, 0 < n → a n ≤ γ ^ n * M := by sorry

end ProjReflGrad.Linear
