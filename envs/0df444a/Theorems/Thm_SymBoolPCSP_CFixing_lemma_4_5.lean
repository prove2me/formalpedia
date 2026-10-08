-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_lemma_4_5
-- name    : SymBoolPCSP.CFixing.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:23.823584+00:00
-- url     : https://prove2.me/theorems/9e34808e-03ff-4904-9ff5-c64eb1818f6d
-- title:
--   Lemma 4.5 — an Alternating-Threshold-excluding relaxation
-- statement:
--   Let $\Gamma$ be a finite, symmetric, folded, idempotent family of Boolean promise relations such that $\mathrm{AT}_L \notin \mathrm{Pol}(\Gamma)$ for some odd $L$. Then there is $k$ such that $\Gamma' = \{(P, Q)\}$ is a relaxation of $\Gamma$ (that is, $\mathrm{Pol}(\Gamma) \subseteq \mathrm{Pol}(P,Q)$) for one of
--
--   1. $P = \mathrm{Ham}_k(\{1\})$, $Q = \mathrm{Ham}_k(\{0, 1, \dots, k-2, k\})$, with $k \ge 3$; or
--   2. $P = \mathrm{Ham}_k(\{0, b\})$, $Q = \mathrm{Ham}_k(\{0, \dots, k-1\})$, with $k \ge 2$ and $b \in \{1, \dots, k-1\}$.
--
--   The relaxation depends only on $\Gamma$, not on the arity of the polymorphism, and supplies the combinatorial constraint used in Lemma 4.10.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, p. 17, Lemma 4.5

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric

namespace SymBoolPCSP.CFixing

/-- Lemma 4.5 (p. 17): if `Γ` is symmetric, folded and idempotent and `AT_L ∉ Pol(Γ)` for some
odd `L`, then `Γ′ = {(P, Q)}` is a relaxation of `Γ` for either
`P = Ham_k({1})`, `Q = Ham_k({0, 1, …, k − 2, k})`, `k ≥ 3`, or
`P = Ham_k({0, b})`, `Q = Ham_k({0, …, k − 1})`, `k ≥ 2`, `b ∈ {1, …, k − 1}`. -/
theorem lemma_4_5 {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hsym : IsSymmetricFamily 𝔸 𝔹) (hfold : IsFoldedFamily 𝔸 𝔹)
    (hidem : IsIdempotentFamily 𝔸 𝔹) (L : ℕ) (hL : Odd L) (hAT : ¬ IsPolymorphism 𝔸 𝔹 (AT L)) :
    ∃ k : ℕ,
      (3 ≤ k ∧ IsRelaxation 𝔸 𝔹 (Ham k {1}) (Ham k (Set.Iic (k - 2) ∪ {k}))) ∨
      (2 ≤ k ∧ ∃ b : ℕ, 1 ≤ b ∧ b ≤ k - 1 ∧
        IsRelaxation 𝔸 𝔹 (Ham k {0, b}) (Ham k (Set.Iic (k - 1)))) := by sorry

end SymBoolPCSP.CFixing
