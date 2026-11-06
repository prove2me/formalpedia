-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_sum_conditions_add_closed
-- name    : SymBoolPCSP.CFixing.sum_conditions_add_closed
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-05T20:17:47.342804+00:00
-- url     : https://prove2.me/theorems/72b9b63d-0f15-4de4-8d46-1fea5bdd32ab
-- title:
--   Sum conditions (1)–(2) make $S_0, S_1$ closed under $+(2n-2)$ and $+(3n-4)$
-- statement:
--   Let $n \ge 2$ and $N \ge 0$, and let $S_0, S_1 \subseteq \mathbb Z_{\ge 0}$ with $0 \in S_0$ and $1 \in S_1$. Assume the sum conditions (1)–(2) of Lemma 4.9 of Brakensiek–Guruswami in the bounded form of the Remark following it: for all $a \in S_0$ and $b_1, \dots, b_n \in S_1$,
--
--   1. $b_1 + \cdots + b_n \in S_0$ whenever $b_1 + \cdots + b_n \le N$, and
--   2. $a + b_1 + \cdots + b_{n-1} \in S_1$ whenever $a + b_1 + \cdots + b_{n-1} \le N$.
--
--   Then both $S_0$ and $S_1$ are closed under adding $2n-2$ and under adding $3n-4$, as long as the result is at most $N$: for $i \in \{0,1\}$ and $t \in \{2n-2,\ 3n-4\}$,
--
--   $$
--   x \in S_i,\ x + t \le N \implies x + t \in S_i .
--   $$
--
--   These closure properties are the facts (6)–(8) derived in the proof of Lemma 4.9 (for $S_1$ the step $3n-4$ is obtained by the same chain). Together with a Frobenius-type closure lemma they give the eventual periodicity of $S_0$ and $S_1$ used in the analysis of polymorphisms avoiding Parity and Alternating-Threshold (Lemma 4.10 ff.).
--
--   **Formalization Note** Tuples $b_1, \dots, b_n$ are functions `Fin n → ℕ`. Taking $N$ large recovers the unbounded conditions of Lemma 4.9.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, §4, proof of Lemma 4.9, facts (3)–(8), pp. 21–22, and the Remark after Lemma 4.9, p. 22

import Mathlib

namespace SymBoolPCSP.CFixing

/-- The sum conditions (1)–(2) of Lemma 4.9 (bounded by `N`), with `n ≥ 2`, `0 ∈ S₀`,
`1 ∈ S₁`, make both `S₀` and `S₁` closed under adding `2n-2` and adding `3n-4`
(as long as the result is at most `N`). -/
theorem sum_conditions_add_closed (n N : ℕ) (hn : 2 ≤ n) (S₀ S₁ : Set ℕ)
    (h0 : 0 ∈ S₀) (h1 : 1 ∈ S₁)
    (hs0 : ∀ b : Fin n → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ≤ N → ∑ i, b i ∈ S₀)
    (hs1 : ∀ a ∈ S₀, ∀ b : Fin (n - 1) → ℕ, (∀ i, b i ∈ S₁) →
      a + ∑ i, b i ≤ N → a + ∑ i, b i ∈ S₁) :
    (∀ x ∈ S₀, x + (2 * n - 2) ≤ N → x + (2 * n - 2) ∈ S₀) ∧
    (∀ x ∈ S₀, x + (3 * n - 4) ≤ N → x + (3 * n - 4) ∈ S₀) ∧
    (∀ x ∈ S₁, x + (2 * n - 2) ≤ N → x + (2 * n - 2) ∈ S₁) ∧
    (∀ x ∈ S₁, x + (3 * n - 4) ≤ N → x + (3 * n - 4) ∈ S₁) := by sorry

end SymBoolPCSP.CFixing
