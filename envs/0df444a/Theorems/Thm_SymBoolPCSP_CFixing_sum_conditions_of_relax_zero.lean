-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_sum_conditions_of_relax_zero
-- name    : SymBoolPCSP.CFixing.sum_conditions_of_relax_zero
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T18:24:25.173793+00:00
-- url     : https://prove2.me/theorems/15145d85-92ba-4b47-b336-2858591b7a17
-- title:
--   Lemma 4.9 sum conditions from the relaxation (Ham_k{0,b}, Ham_k{0..k-1})
-- statement:
--   Let $1 \le b \le k - 1$, put $n = k - b + 1$, and let $f : \{0,1\}^L \to \{0,1\}$ be a folded polymorphism of the promise relation $\big(\mathrm{Ham}_k(\{0, b\}), \mathrm{Ham}_k(\{0, \dots, k-1\})\big)$. Fix $T \subseteq [L]$ and, for $\beta \in \{0,1\}$, let $S_\beta$ be the set of $s \in \mathbb{N}$ such that $f(e_X) = \beta$ for every $X \subseteq T$ with $|X| = s$, where $e_X$ is the indicator vector of $X$. Then:
--
--   1. if $b_1, \dots, b_n \in S_1$, then $b_1 + \cdots + b_n \in S_0$;
--   2. if $a \in S_0$ and $b_1, \dots, b_{n-1} \in S_1$, then $a + b_1 + \cdots + b_{n-1} \in S_1$.
--
--   These are conditions (1) and (2) of Lemma 4.9 for the second relaxation produced by Lemma 4.5 (Case 2 of the proof of Lemma 4.10).
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, proof of Lemma 4.10, Case 2, pp. 22–23

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric
namespace SymBoolPCSP.CFixing

/-- Sum conditions from the second relaxation of Lemma 4.5: let `1 ≤ b ≤ k − 1`, `n = k − b + 1`, and let `f` be a folded polymorphism of `(Ham_k({0, b}), Ham_k({0,…,k−1}))`. Fix `T ⊆ [L]` and let `S_β` (`β ∈ {0,1}`) be the set of `s` such that `f(e_X) = β` for every `X ⊆ T` with `|X| = s`. Then any sum of `n` elements of `S₁` lies in `S₀`, and `a + b₁ + ⋯ + b_{n−1} ∈ S₁` whenever `a ∈ S₀` and all `bᵢ ∈ S₁`. -/
theorem sum_conditions_of_relax_zero {k b L : ℕ} (hb1 : 1 ≤ b) (hbk : b ≤ k - 1)
    (f : (Fin L → Bool) → Bool) (hfold : IsFolded f)
    (hf : PolOf (Ham k {0, b}) (Ham k (Set.Iic (k - 1))) f)
    (T : Finset (Fin L)) (S₀ S₁ : Set ℕ)
    (hS₀ : ∀ s, s ∈ S₀ ↔ ∀ X ⊆ T, X.card = s → f (indicator X) = false)
    (hS₁ : ∀ s, s ∈ S₁ ↔ ∀ X ⊆ T, X.card = s → f (indicator X) = true) :
    (∀ β : Fin (k - b + 1) → ℕ, (∀ i, β i ∈ S₁) → ∑ i, β i ∈ S₀) ∧
    (∀ a ∈ S₀, ∀ β : Fin (k - b + 1 - 1) → ℕ, (∀ i, β i ∈ S₁) → a + ∑ i, β i ∈ S₁) := by sorry

end SymBoolPCSP.CFixing
