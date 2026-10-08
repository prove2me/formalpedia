-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_lemma_2_13_1
-- name    : SymBoolPCSP.CFixing.lemma_2_13_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:28:52.489179+00:00
-- url     : https://prove2.me/theorems/cde05dcb-a18e-4987-b4f5-38d942c2a14c
-- title:
--   Lemma 2.13(1) — Pol(Γ) = Pol(Γ′) ∪ ¬Pol(Γ″)
-- statement:
--   Let $\Gamma = \{(P_i, Q_i)\}$ be a finite family of Boolean promise relations that is non-degenerate (all of its polymorphisms are non-degenerate) and has at least one non-idempotent polymorphism. Let
--   $$\Gamma' = \Gamma \cup \{\text{SET-ZERO}, \text{SET-ONE}\}, \qquad \Gamma'' = (\neg\Gamma) \cup \{\text{SET-ZERO}, \text{SET-ONE}\},$$
--   where $\neg\Gamma = ((P_i, \neg Q_i))$. Then
--   $$\mathrm{Pol}(\Gamma) = \mathrm{Pol}(\Gamma') \cup \neg\,\mathrm{Pol}(\Gamma''), \qquad \neg\,\mathrm{Pol}(\Delta) = \{\neg g : g \in \mathrm{Pol}(\Delta)\}.$$
--
--   It reduces the study of all polymorphisms of $\Gamma$ to the idempotent polymorphisms of two families, which is how the non-idempotent case of Theorem 4.13 is handled.
--
--   **Formalization Note** The equality of sets is stated arity by arity: for every $L$ and $f$, $f \in \mathrm{Pol}(\Gamma)$ iff $f \in \mathrm{Pol}(\Gamma')$ or $f = \neg g$ for some $g \in \mathrm{Pol}(\Gamma'')$. $\neg\Gamma$ is defined for every family; that $P_i \subseteq \neg Q_i$ under the hypotheses is Proposition 2.12 and is not assumed. Item 2 of the lemma (transfer of polynomial-time tractability) is a complexity statement and is not formalized.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, p. 11, Lemma 2.13 item 1

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric

namespace SymBoolPCSP.CFixing

/-- Lemma 2.13, item 1 (p. 11): if `Γ` is non-degenerate and has a non-idempotent polymorphism,
then `Pol(Γ) = Pol(Γ′) ∪ ¬Pol(Γ″)`, where `Γ′ = Γ ∪ {SET-ZERO, SET-ONE}`,
`Γ″ = (¬Γ) ∪ {SET-ZERO, SET-ONE}` and `¬Pol(Δ) = {¬g : g ∈ Pol(Δ)}`. -/
theorem lemma_2_13_1 {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hnd : IsNonDegenerateFamily 𝔸 𝔹)
    (hex : ∃ (L : ℕ) (f : (Fin L → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f ∧ ¬ IsIdempotent f) :
    ∀ (L : ℕ) (f : (Fin L → Bool) → Bool),
      IsPolymorphism 𝔸 𝔹 f ↔
        (IsPolymorphism (withConsts 𝔸) (withConsts 𝔹) f ∨
          ∃ g : (Fin L → Bool) → Bool,
            IsPolymorphism (withConsts 𝔸) (withConsts (negStruct 𝔹)) g ∧ f = fun x => !g x) := by sorry

end SymBoolPCSP.CFixing
