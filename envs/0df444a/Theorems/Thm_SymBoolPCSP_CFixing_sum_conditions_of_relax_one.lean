-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_sum_conditions_of_relax_one
-- name    : SymBoolPCSP.CFixing.sum_conditions_of_relax_one
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T18:24:27.726203+00:00
-- url     : https://prove2.me/theorems/0ece19ea-b40e-4ac8-b9b0-82ae848f3bc5
-- title:
--   Lemma 4.9 sum conditions from the relaxation (Ham_k{1}, Ham_k({0..k-2} ∪ {k}))
-- statement:
--   Let $k \ge 2$ and let $f : \{0,1\}^L \to \{0,1\}$ be a folded polymorphism of the promise relation $\big(\mathrm{Ham}_k(\{1\}), \mathrm{Ham}_k(\{0, \dots, k-2\} \cup \{k\})\big)$. Fix $T \subseteq [L]$ and, for $\beta \in \{0,1\}$, let $S_\beta$ be the set of $s \in \mathbb{N}$ such that $f(e_X) = \beta$ for every $X \subseteq T$ with $|X| = s$, where $e_X$ is the indicator vector of $X$. Then:
--
--   1. if $b_1, \dots, b_{k-1} \in S_1$, then $b_1 + \cdots + b_{k-1} \in S_0$;
--   2. if $a \in S_0$ and $b_1, \dots, b_{k-2} \in S_1$, then $a + b_1 + \cdots + b_{k-2} \in S_1$.
--
--   These are conditions (1) and (2) of Lemma 4.9 with $n = k - 1$, for the first relaxation produced by Lemma 4.5 (Case 1 of the proof of Lemma 4.10).
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, proof of Lemma 4.10, Case 1, p. 22

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric
namespace SymBoolPCSP.CFixing

/-- Sum conditions from the first relaxation of Lemma 4.5: let `k ≥ 2` and let `f` be a folded polymorphism of `(Ham_k({1}), Ham_k({0,…,k−2} ∪ {k}))`. Fix `T ⊆ [L]` and let `S_β` (`β ∈ {0,1}`) be the set of `s` such that `f(e_X) = β` for every `X ⊆ T` with `|X| = s`. Then any sum of `k − 1` elements of `S₁` lies in `S₀`, and `a + b₁ + ⋯ + b_{k−2} ∈ S₁` whenever `a ∈ S₀` and all `bᵢ ∈ S₁`. -/
theorem sum_conditions_of_relax_one {k L : ℕ} (hk : 2 ≤ k) (f : (Fin L → Bool) → Bool)
    (hfold : IsFolded f) (hf : PolOf (Ham k {1}) (Ham k (Set.Iic (k - 2) ∪ {k})) f)
    (T : Finset (Fin L)) (S₀ S₁ : Set ℕ)
    (hS₀ : ∀ s, s ∈ S₀ ↔ ∀ X ⊆ T, X.card = s → f (indicator X) = false)
    (hS₁ : ∀ s, s ∈ S₁ ↔ ∀ X ⊆ T, X.card = s → f (indicator X) = true) :
    (∀ b : Fin (k - 1) → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ∈ S₀) ∧
    (∀ a ∈ S₀, ∀ b : Fin (k - 1 - 1) → ℕ, (∀ i, b i ∈ S₁) → a + ∑ i, b i ∈ S₁) := by sorry

end SymBoolPCSP.CFixing
