-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_lemma_4_12
-- name    : SymBoolPCSP.CFixing.lemma_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:14.636732+00:00
-- url     : https://prove2.me/theorems/d24be593-d7a8-41b5-b375-ff61c2305646
-- title:
--   Lemma 4.12 — idempotent case: avoiding Par, AT and Maj forces C(Γ)-fixing polymorphisms
-- statement:
--   Let $\Gamma$ be a finite, symmetric, folded, idempotent family of Boolean promise relations such that $\mathrm{Par}_{L_1}, \mathrm{AT}_{L_2}, \mathrm{Maj}_{L_3} \notin \mathrm{Pol}(\Gamma)$ for some odd $L_1, L_2, L_3$. Then there is $C(\Gamma) \in \mathbb{N}$ such that every polymorphism $f$ of $\Gamma$ is $C(\Gamma)$-fixing: there is a set $S$ of at most $C(\Gamma)$ coordinates such that
--   $$x_i = 0 \text{ for all } i \in S \implies f(x) = f(0, \dots, 0).$$
--
--   The constant does not depend on the arity of $f$. This is the idempotent case of Theorem 4.13.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, p. 24, Lemma 4.12

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric

namespace SymBoolPCSP.CFixing

/-- Lemma 4.12 (p. 24): if `Γ` is finite, symmetric, folded and idempotent and
`Par_{L₁}, AT_{L₂}, Maj_{L₃} ∉ Pol(Γ)` for some odd `L₁, L₂, L₃`, then there is `C(Γ) ∈ ℕ` such
that every polymorphism of `Γ` is `C(Γ)`-fixing. -/
theorem lemma_4_12 {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hsym : IsSymmetricFamily 𝔸 𝔹) (hfold : IsFoldedFamily 𝔸 𝔹)
    (hidem : IsIdempotentFamily 𝔸 𝔹) (L₁ L₂ L₃ : ℕ) (hL₁ : Odd L₁) (hL₂ : Odd L₂)
    (hL₃ : Odd L₃) (hPar : ¬ IsPolymorphism 𝔸 𝔹 (Par L₁)) (hAT : ¬ IsPolymorphism 𝔸 𝔹 (AT L₂))
    (hMaj : ¬ IsPolymorphism 𝔸 𝔹 (Maj L₃)) :
    ∃ C : ℕ, ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f → IsCFixing C f := by sorry

end SymBoolPCSP.CFixing
