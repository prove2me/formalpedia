-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_corollary_4_11
-- name    : SymBoolPCSP.CFixing.corollary_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:46.042293+00:00
-- url     : https://prove2.me/theorems/dddc0649-ffda-4f8c-beda-a3afe5bd07ed
-- title:
--   Corollary 4.11 — at most c(Γ) disjoint sets S_i with f(e_{S_i}) = 1
-- statement:
--   Let $\Gamma$ satisfy the hypotheses of Lemma 4.10 and let $c$ be a constant as in Lemma 4.10, i.e. $|\{i : f(e_i) = 1\}| \le c$ for every polymorphism $f$ of $\Gamma$. Let $f : \{0,1\}^L \to \{0,1\}$ be a polymorphism of $\Gamma$ and let $S_1, \dots, S_\ell \subseteq \{1, \dots, L\}$ be pairwise disjoint with $f(e_{S_i}) = 1$ for all $i$. Then
--   $$\ell \le c.$$
--
--   The bound on singletons thus extends to any family of disjoint sets on which $f$ is $1$, which is how Lemma 4.12 bounds the number of relevant coordinates.
--
--   **Formalization Note** "The same $c(\Gamma)$ as in Lemma 4.10" is stated as: every constant $c$ satisfying the conclusion of Lemma 4.10 also bounds $\ell$.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, p. 24, Corollary 4.11

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric

namespace SymBoolPCSP.CFixing

/-- Corollary 4.11 (p. 24): under the hypotheses of Lemma 4.10, let `c` be a constant as in
Lemma 4.10. If `f ∈ Pol(Γ)` has arity `L` and `S₁, …, S_ℓ ⊆ [L]` are pairwise disjoint with
`f(e_{S_i}) = 1` for all `i`, then `ℓ ≤ c`. -/
theorem corollary_4_11 {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hsym : IsSymmetricFamily 𝔸 𝔹) (hfold : IsFoldedFamily 𝔸 𝔹)
    (hidem : IsIdempotentFamily 𝔸 𝔹) (L₁ L₂ : ℕ) (hL₁ : Odd L₁) (hL₂ : Odd L₂)
    (hPar : ¬ IsPolymorphism 𝔸 𝔹 (Par L₁)) (hAT : ¬ IsPolymorphism 𝔸 𝔹 (AT L₂))
    (c : ℕ) (hc : ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f →
      (Finset.univ.filter (fun i : Fin L => f (indicator {i}) = true)).card ≤ c) :
    ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f →
      ∀ (ℓ : ℕ) (S : Fin ℓ → Finset (Fin L)), (∀ i j, i ≠ j → Disjoint (S i) (S j)) →
        (∀ i, f (indicator (S i)) = true) → ℓ ≤ c := by sorry

end SymBoolPCSP.CFixing
