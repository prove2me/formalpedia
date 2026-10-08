-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_lemma_4_9
-- name    : SymBoolPCSP.CFixing.lemma_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:56.028516+00:00
-- url     : https://prove2.me/theorems/7bae1118-2f50-403f-be03-bb2bce36f1a8
-- title:
--   Lemma 4.9 — two sets closed under the sums (1)–(2) meet, or contain all large evens/odds
-- statement:
--   Let $n$ be a positive integer. Say that $S_0, S_1 \subseteq \mathbb{Z}_{\ge 0}$ satisfy (1)–(2) if for all $a \in S_0$ and all $b_1, \dots, b_n \in S_1$ (not necessarily distinct)
--   $$b_1 + \dots + b_n \in S_0 \quad (1), \qquad a + b_1 + \dots + b_{n-1} \in S_1 \quad (2).$$
--
--   1. If $n$ is odd, there is $A(n) \in \mathbb{Z}_{\ge 0}$ such that $A(n) \in S_0 \cap S_1$ for every pair satisfying (1)–(2) with $0 \in S_0$ and $1 \in S_1$.
--   2. If $n$ is even, there is $d(n) \in \mathbb{Z}_{\ge 0}$ such that for every such pair, $S_0$ contains all even integers $\ge d(n)$ and $S_1$ contains all odd integers $\ge d(n)$.
--
--   This additive-combinatorics lemma is what forces a polymorphism with many coordinates $i$ having $f(e_i) = 1$ to behave like parity (Lemma 4.10).
--
--   **Formalization Note** The constants depend on $n$ only, not on $S_0, S_1$, as the notation $A(n)$, $d(n)$ and the remark after the lemma state; the quantifiers are ordered accordingly.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, p. 21, Lemma 4.9

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric

namespace SymBoolPCSP.CFixing

/-- Lemma 4.9 (p. 21). For a positive integer `n`, say that `S₀, S₁ ⊆ ℤ_{≥0}` satisfy (1)–(2) if
for all `a ∈ S₀` and `b₁, …, bₙ ∈ S₁`: (1) `b₁ + ⋯ + bₙ ∈ S₀` and (2) `a + b₁ + ⋯ + b_{n−1} ∈ S₁`.
If `n` is odd there is `A(n)` lying in `S₀ ∩ S₁` for every such pair with `0 ∈ S₀`, `1 ∈ S₁`; if `n`
is even there is `d(n)` such that every such pair has all even integers `≥ d(n)` in `S₀` and all
odd integers `≥ d(n)` in `S₁`. The constants depend on `n` only. -/
theorem lemma_4_9 (n : ℕ) (hn : 0 < n) :
    (Odd n → ∃ A : ℕ, ∀ S₀ S₁ : Set ℕ, 0 ∈ S₀ → 1 ∈ S₁ →
      (∀ b : Fin n → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ∈ S₀) →
      (∀ a ∈ S₀, ∀ b : Fin (n - 1) → ℕ, (∀ i, b i ∈ S₁) → a + ∑ i, b i ∈ S₁) →
      A ∈ S₀ ∧ A ∈ S₁) ∧
    (Even n → ∃ d : ℕ, ∀ S₀ S₁ : Set ℕ, 0 ∈ S₀ → 1 ∈ S₁ →
      (∀ b : Fin n → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ∈ S₀) →
      (∀ a ∈ S₀, ∀ b : Fin (n - 1) → ℕ, (∀ i, b i ∈ S₁) → a + ∑ i, b i ∈ S₁) →
      (∀ m : ℕ, d ≤ m → Even m → m ∈ S₀) ∧ (∀ m : ℕ, d ≤ m → Odd m → m ∈ S₁)) := by sorry

end SymBoolPCSP.CFixing
