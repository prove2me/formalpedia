-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_lemma_4_10
-- name    : SymBoolPCSP.CFixing.lemma_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:04.255555+00:00
-- url     : https://prove2.me/theorems/affd63a4-1c56-4e20-bb8f-e76c4992de22
-- title:
--   Lemma 4.10 — avoiding Parity and Alternating-Threshold bounds |{i : f(e_i) = 1}|
-- statement:
--   Let $\Gamma$ be a finite, symmetric, folded, idempotent family of Boolean promise relations such that $\mathrm{Par}_{L_1} \notin \mathrm{Pol}(\Gamma)$ and $\mathrm{AT}_{L_2} \notin \mathrm{Pol}(\Gamma)$ for some odd $L_1, L_2$. Then there is $c(\Gamma) \in \mathbb{N}$ such that for every $L$ and every polymorphism $f : \{0,1\}^L \to \{0,1\}$ of $\Gamma$,
--   $$\big|\{i \in \{1, \dots, L\} : f(e_i) = 1\}\big| \le c(\Gamma),$$
--   where $e_i$ is the $i$-th unit vector.
--
--   The constant is uniform over all polymorphisms of all arities; this uniformity is the point of the lemma.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, p. 22, Lemma 4.10

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric

namespace SymBoolPCSP.CFixing

/-- Lemma 4.10 (p. 22): if `Γ` is finite, symmetric, folded and idempotent and
`Par_{L₁}, AT_{L₂} ∉ Pol(Γ)` for some odd `L₁, L₂`, then there is `c(Γ) ∈ ℕ` such that every
polymorphism `f` of `Γ`, of any arity `L`, has `|{i ∈ [L] : f(e_i) = 1}| ≤ c(Γ)`. -/
theorem lemma_4_10 {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hsym : IsSymmetricFamily 𝔸 𝔹) (hfold : IsFoldedFamily 𝔸 𝔹)
    (hidem : IsIdempotentFamily 𝔸 𝔹) (L₁ L₂ : ℕ) (hL₁ : Odd L₁) (hL₂ : Odd L₂)
    (hPar : ¬ IsPolymorphism 𝔸 𝔹 (Par L₁)) (hAT : ¬ IsPolymorphism 𝔸 𝔹 (AT L₂)) :
    ∃ c : ℕ, ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f →
      (Finset.univ.filter (fun i : Fin L => f (indicator {i}) = true)).card ≤ c := by sorry

end SymBoolPCSP.CFixing
