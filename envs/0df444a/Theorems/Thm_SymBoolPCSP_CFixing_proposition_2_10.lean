-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_proposition_2_10
-- name    : SymBoolPCSP.CFixing.proposition_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:28:51.437246+00:00
-- url     : https://prove2.me/theorems/781d28e6-6b00-4282-afd9-342cb0c3c686
-- title:
--   Proposition 2.10 — idempotent polymorphisms of Γ are Pol(Γ ∪ {SET-ZERO, SET-ONE})
-- statement:
--   Let $\Gamma$ be a finite family of Boolean promise relations, and let $\Gamma \cup \{\text{SET-ZERO}, \text{SET-ONE}\}$ be $\Gamma$ together with the unary promise relations $(\{(0)\},\{(0)\})$ and $(\{(1)\},\{(1)\})$. For every $L$ and every $f : \{0,1\}^L \to \{0,1\}$,
--   $$f \in \mathrm{Pol}(\Gamma) \text{ and } f \text{ is idempotent} \iff f \in \mathrm{Pol}(\Gamma \cup \{\text{SET-ZERO}, \text{SET-ONE}\}).$$
--
--   Adding the two constant relations is therefore the standard way to restrict attention to idempotent polymorphisms.
--
--   **Formalization Note** The printed statement says "the set of idempotent promise relations of $\Gamma$"; its proof shows that "polymorphisms" is meant, and that is what is stated.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, p. 11, Proposition 2.10

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric

namespace SymBoolPCSP.CFixing

/-- Proposition 2.10 (p. 11): for any family `Γ`, the idempotent polymorphisms of `Γ` are exactly
the polymorphisms of `Γ ∪ {SET-ZERO, SET-ONE}`. -/
theorem proposition_2_10 {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) {L : ℕ} (f : (Fin L → Bool) → Bool) :
    (IsPolymorphism 𝔸 𝔹 f ∧ IsIdempotent f) ↔
      IsPolymorphism (withConsts 𝔸) (withConsts 𝔹) f := by sorry

end SymBoolPCSP.CFixing
