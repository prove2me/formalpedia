-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_lemma_4_9_bounded_explicit
-- name    : SymBoolPCSP.CFixing.lemma_4_9_bounded_explicit
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-05T20:17:49.81071+00:00
-- url     : https://prove2.me/theorems/9511efc4-2a95-4305-bad2-0e2cb14cb4f7
-- title:
--   Lemma 4.9 (bounded, explicit constant $1+(2n-2)(3n-4)$)
-- statement:
--   This is Lemma 4.9 of Brakensiek–Guruswami in the bounded form of the Remark following it, with an explicit constant.
--
--   Let $n \ge 1$, $N \ge 0$, and let $S_0, S_1 \subseteq \mathbb Z_{\ge 0}$ with $0 \in S_0$ and $1 \in S_1$, satisfying the bounded sum conditions: for all $a \in S_0$ and $b_1, \dots, b_n \in S_1$,
--
--   1. $b_1 + \cdots + b_n \in S_0$ whenever this sum is at most $N$, and
--   2. $a + b_1 + \cdots + b_{n-1} \in S_1$ whenever this sum is at most $N$.
--
--   Put
--
--   $$
--   c(n) = \begin{cases} 0, & n = 1,\\ 1 + (2n-2)(3n-4), & n \ge 2. \end{cases}
--   $$
--
--   Then:
--
--   1. if $n$ is odd and $c(n) \le N$, then $c(n) \in S_0 \cap S_1$;
--   2. if $n$ is even, then every even $m$ with $c(n) \le m \le N$ lies in $S_0$, and every odd $m$ with $c(n) \le m \le N$ lies in $S_1$.
--
--   The constant depends on $n$ only, which is exactly what Lemma 4.9 (unbounded, $N$ arbitrary) and its Remark (sets inside $\{0,\dots,N\}$) require; both follow directly from this statement. The explicit value of $c(n)$ makes the bounds $A(n)$, $d(n)$ quantitative for later use (e.g. the constant $c(\Gamma)$ in Lemma 4.10).
--
--   **Formalization Note** Tuples are functions `Fin n → ℕ` and `Fin (n-1) → ℕ`; the constant is written as `if n = 1 then 0 else 1 + (2n-2)(3n-4)` with natural-number subtraction, which is exact for $n \ge 2$.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, §4, Lemma 4.9 and the Remark after it, pp. 21–22

import Mathlib

namespace SymBoolPCSP.CFixing

/-- Bounded form of Lemma 4.9 of Brakensiek–Guruswami, with the explicit constant `c(n) = 0` for `n = 1` and
`c(n) = 1 + (2n-2)(3n-4)` for `n ≥ 2`. -/
theorem lemma_4_9_bounded_explicit (n N : ℕ) (hn : 0 < n) (S₀ S₁ : Set ℕ)
    (h0 : 0 ∈ S₀) (h1 : 1 ∈ S₁)
    (hs0 : ∀ b : Fin n → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ≤ N → ∑ i, b i ∈ S₀)
    (hs1 : ∀ a ∈ S₀, ∀ b : Fin (n - 1) → ℕ, (∀ i, b i ∈ S₁) →
      a + ∑ i, b i ≤ N → a + ∑ i, b i ∈ S₁) :
    (Odd n → (if n = 1 then 0 else 1 + (2 * n - 2) * (3 * n - 4)) ≤ N →
      (if n = 1 then 0 else 1 + (2 * n - 2) * (3 * n - 4)) ∈ S₀ ∧
      (if n = 1 then 0 else 1 + (2 * n - 2) * (3 * n - 4)) ∈ S₁) ∧
    (Even n → ∀ M : ℕ, (if n = 1 then 0 else 1 + (2 * n - 2) * (3 * n - 4)) ≤ M → M ≤ N →
      (Even M → M ∈ S₀) ∧ (Odd M → M ∈ S₁)) := by sorry

end SymBoolPCSP.CFixing
