-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_lemma_4_7
-- name    : SymBoolPCSP.CFixing.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:09.204166+00:00
-- url     : https://prove2.me/theorems/e2b6b99a-43e2-44ea-ab74-82ae668c6b3e
-- title:
--   Lemma 4.7 — a Majority-excluding relaxation
-- statement:
--   Let $\Gamma$ be a finite, symmetric, folded, idempotent family of Boolean promise relations such that $\mathrm{Maj}_L \notin \mathrm{Pol}(\Gamma)$ for some odd $L$. Then there is $k$ such that $\Gamma' = \{(P, Q)\}$ is a relaxation of $\Gamma$ for one of
--
--   1. $P = \mathrm{Ham}_k(\{(k+1)/2\})$, $Q = \mathrm{Ham}_k(\{0, 1, \dots, k-1\})$, with $k \ge 3$ odd; or
--   2. $P = \mathrm{Ham}_k(\{1, k\})$, $Q = \mathrm{Ham}_k(\{0, 1, \dots, k\} \setminus \{b\})$, with $k \ge 3$ and $b \in \{2, \dots, k-1\}$.
--
--   Lemma 4.12 analyses the polymorphisms of these two relaxations.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, p. 19, Lemma 4.7

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric

namespace SymBoolPCSP.CFixing

/-- Lemma 4.7 (p. 19): if `Γ` is symmetric, folded and idempotent and `Maj_L ∉ Pol(Γ)` for some
odd `L`, then `Γ′ = {(P, Q)}` is a relaxation of `Γ` for either
`P = Ham_k({(k + 1)/2})`, `Q = Ham_k({0, 1, …, k − 1})`, `k ≥ 3` odd, or
`P = Ham_k({1, k})`, `Q = Ham_k({0, 1, …, k} ∖ {b})`, `k ≥ 3`, `b ∈ {2, …, k − 1}`. -/
theorem lemma_4_7 {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hsym : IsSymmetricFamily 𝔸 𝔹) (hfold : IsFoldedFamily 𝔸 𝔹)
    (hidem : IsIdempotentFamily 𝔸 𝔹) (L : ℕ) (hL : Odd L) (hMaj : ¬ IsPolymorphism 𝔸 𝔹 (Maj L)) :
    ∃ k : ℕ,
      (3 ≤ k ∧ Odd k ∧ IsRelaxation 𝔸 𝔹 (Ham k {(k + 1) / 2}) (Ham k (Set.Iic (k - 1)))) ∨
      (3 ≤ k ∧ ∃ b : ℕ, 2 ≤ b ∧ b ≤ k - 1 ∧
        IsRelaxation 𝔸 𝔹 (Ham k {1, k}) (Ham k (Set.Iic k \ {b}))) := by sorry

end SymBoolPCSP.CFixing
