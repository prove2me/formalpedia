-- Prove2me | Theorems.Thm_SymBoolPCSP_PolChar_lemma_6_7
-- name    : SymBoolPCSP.PolChar.lemma_6_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:57.324587+00:00
-- url     : https://prove2.me/theorems/830c4a28-66d8-4550-92a7-c09dfedcd8ec
-- title:
--   Lemma 6.7 — a projection-closed finitizable family containing id_D is Pol(Γ) for a finite Γ
-- statement:
--   Let $D$ be a finite domain and let $\mathcal F$ be a family of functions over $D$ which is projection-closed and finitizable and contains the identity $\mathrm{id}_D$. Then there is a family $\Gamma$ of finitely many promise relations over $D$ such that
--   $$\mathrm{Pol}(\Gamma) = \mathcal F.$$
--
--   This is the sufficiency half of Theorem 6.5, a finite-signature analogue of Pippenger's characterization of polymorphism families.
--
--   **Formalization Note** The finite family is existential together with its signature: a finite type `τ`, arities `ar : τ → ℕ`, and structures `𝔸 ⊆ 𝔹`. The equality $\mathrm{Pol}(\Gamma) = \mathcal F$ is asserted at every arity $L \ge 1$. No assumption $|D| \ge 2$ is made.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, p. 29, Lemma 6.7 (proof pp. 29–30)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_PolChar_Basic

namespace SymBoolPCSP.PolChar

open PCSPBLPAff.Symmetric

/-- Lemma 6.7 (p. 29): if a family `F` of functions over a finite domain `D` is
projection-closed, finitizable and contains `id_D`, then there is a finite family `Γ` of
promise relations (a finite signature `τ` with arities `ar` and structures `𝔸 ⊆ 𝔹`) with
`Pol(Γ) = F` at every arity `L ≥ 1`. -/
theorem lemma_6_7 {D : Type} [Fintype D] [DecidableEq D] (F : FunFamily D)
    (hpc : ProjectionClosed F) (hfin : Finitizable F) (hid : ContainsId F) :
    ∃ (τ : Type) (_ : Fintype τ) (ar : τ → ℕ) (𝔸 𝔹 : RelStruct τ ar D),
      (∀ R : τ, 𝔸.rel R ⊆ 𝔹.rel R) ∧ ∀ L : ℕ, 0 < L → Pol 𝔸 𝔹 L = F L := by sorry

end SymBoolPCSP.PolChar
