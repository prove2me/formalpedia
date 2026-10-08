-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_remark_4_9
-- name    : SymBoolPCSP.CFixing.remark_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:57.893696+00:00
-- url     : https://prove2.me/theorems/cbeff780-842e-47ef-91b3-be06e1b7ea58
-- title:
--   Remark after Lemma 4.9 — the bounded version with the same A(n), d(n)
-- statement:
--   Let $n$ be a positive integer. There are constants $A(n)$ ($n$ odd) and $d(n)$ ($n$ even) that satisfy Lemma 4.9 and in addition the following bounded version. Let $N$ be a positive integer and $S_0, S_1 \subseteq \{0, \dots, N\}$ with $0 \in S_0$, $1 \in S_1$, such that (1) and (2) of Lemma 4.9 hold whenever the sum on the left is at most $N$. Then
--
--   1. for odd $n$: if $A(n) \le N$, then $A(n) \in S_0 \cap S_1$;
--   2. for even $n$: if $d(n) \le N$, then every even $m$ with $d(n) \le m \le N$ lies in $S_0$ and every odd such $m$ lies in $S_1$.
--
--   This is the form in which Lemma 4.9 is applied in Lemma 4.10, with $N$ the number of coordinates $i$ with $f(e_i) = 1$.
--
--   **Formalization Note** The remark's "independent of $S_1, S_2$" is a typo for $S_0, S_1$. The statement asserts one constant serving both the unbounded lemma and its bounded version for every $N$.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, p. 22, Remark after Lemma 4.9

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric

namespace SymBoolPCSP.CFixing

/-- Remark after Lemma 4.9 (p. 22): the constants `A(n)`, `d(n)` of Lemma 4.9 also serve the
bounded version, in which `S₀, S₁ ⊆ {0, …, N}` and (1)–(2) are only required when the sum is at
most `N`: if `A(n) ≤ N` then `A(n) ∈ S₀ ∩ S₁` (odd `n`), and if `d(n) ≤ N` then every even
`m ∈ [d(n), N]` lies in `S₀` and every odd `m ∈ [d(n), N]` in `S₁` (even `n`). -/
theorem remark_4_9 (n : ℕ) (hn : 0 < n) :
    (Odd n → ∃ A : ℕ,
      (∀ S₀ S₁ : Set ℕ, 0 ∈ S₀ → 1 ∈ S₁ →
        (∀ b : Fin n → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ∈ S₀) →
        (∀ a ∈ S₀, ∀ b : Fin (n - 1) → ℕ, (∀ i, b i ∈ S₁) → a + ∑ i, b i ∈ S₁) →
        A ∈ S₀ ∧ A ∈ S₁) ∧
      (∀ N : ℕ, 0 < N → A ≤ N → ∀ S₀ S₁ : Set ℕ, S₀ ⊆ Set.Iic N → S₁ ⊆ Set.Iic N →
        0 ∈ S₀ → 1 ∈ S₁ →
        (∀ b : Fin n → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ≤ N → ∑ i, b i ∈ S₀) →
        (∀ a ∈ S₀, ∀ b : Fin (n - 1) → ℕ, (∀ i, b i ∈ S₁) →
          a + ∑ i, b i ≤ N → a + ∑ i, b i ∈ S₁) →
        A ∈ S₀ ∧ A ∈ S₁)) ∧
    (Even n → ∃ d : ℕ,
      (∀ S₀ S₁ : Set ℕ, 0 ∈ S₀ → 1 ∈ S₁ →
        (∀ b : Fin n → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ∈ S₀) →
        (∀ a ∈ S₀, ∀ b : Fin (n - 1) → ℕ, (∀ i, b i ∈ S₁) → a + ∑ i, b i ∈ S₁) →
        (∀ m : ℕ, d ≤ m → Even m → m ∈ S₀) ∧ (∀ m : ℕ, d ≤ m → Odd m → m ∈ S₁)) ∧
      (∀ N : ℕ, 0 < N → d ≤ N → ∀ S₀ S₁ : Set ℕ, S₀ ⊆ Set.Iic N → S₁ ⊆ Set.Iic N →
        0 ∈ S₀ → 1 ∈ S₁ →
        (∀ b : Fin n → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ≤ N → ∑ i, b i ∈ S₀) →
        (∀ a ∈ S₀, ∀ b : Fin (n - 1) → ℕ, (∀ i, b i ∈ S₁) →
          a + ∑ i, b i ≤ N → a + ∑ i, b i ∈ S₁) →
        (∀ m : ℕ, d ≤ m → m ≤ N → Even m → m ∈ S₀) ∧
        (∀ m : ℕ, d ≤ m → m ≤ N → Odd m → m ∈ S₁))) := by sorry

end SymBoolPCSP.CFixing
