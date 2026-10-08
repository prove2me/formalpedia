-- Prove2me | Theorems.Thm_SymBoolPCSP_PolChar_theorem_6_5
-- name    : SymBoolPCSP.PolChar.theorem_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:30.433472+00:00
-- url     : https://prove2.me/theorems/4477dc6f-44ec-4f19-87fa-e655d3ab86db
-- title:
--   Theorem 6.5 — F = Pol(Γ) for a finite Γ iff F is projection-closed, finitizable and contains id_D
-- statement:
--   Let $D$ be a finite domain and let $\mathcal F$ be a family of functions over $D$. Then
--   $$\exists\, \Gamma \text{ finite family of promise relations with } \mathcal F = \mathrm{Pol}(\Gamma) \iff \mathcal F \text{ is projection-closed, finitizable, and } \mathrm{id}_D \in \mathcal F.$$
--   Here a promise relation is a pair $(P, Q)$ of relations of the same arity with $P \subseteq Q$, a projection of $f : D^L \to D$ along $\pi : [L] \to [R]$ is $f^\pi(y) = f(y_{\pi(1)}, \dots, y_{\pi(L)})$, and $\mathcal F$ is finitizable if some finite arity $R$ decides membership of every $f$ through its projections $f^\pi$, $\pi : [L] \to [R]$.
--
--   The theorem says that the sets of polymorphisms of finite promise templates are exactly the families singled out by three closure-type conditions, so questions about $\mathrm{PCSP}(\Gamma)$ phrased through polymorphisms can be phrased about such families directly.
--
--   **Formalization Note** A finite family $\Gamma$ is a finite signature `τ` with arities `ar` and structures `𝔸 𝔹 : RelStruct τ ar D` with `𝔸.rel R ⊆ 𝔹.rel R`, all existentially quantified. Arities of functions are positive: $\mathcal F = \mathrm{Pol}(\Gamma)$ is compared at every $L \ge 1$, and projection-closure and finitizability (with finitized arity $R \ge 1$) are imposed only on positive arities; the paper's $L, R \in \mathbb N$ is read as positive integers.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, p. 29, Theorem 6.5

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_PolChar_Basic

namespace SymBoolPCSP.PolChar

open PCSPBLPAff.Symmetric

/-- Theorem 6.5 (p. 29): a family `F` of functions over a finite domain `D` equals `Pol(Γ)` (at
every arity `L ≥ 1`) for some finite family `Γ` of promise relations if and only if `F` is
projection-closed, finitizable and contains `id_D`. -/
theorem theorem_6_5 {D : Type} [Fintype D] [DecidableEq D] (F : FunFamily D) :
    (∃ (τ : Type) (_ : Fintype τ) (ar : τ → ℕ) (𝔸 𝔹 : RelStruct τ ar D),
        (∀ R : τ, 𝔸.rel R ⊆ 𝔹.rel R) ∧ ∀ L : ℕ, 0 < L → F L = Pol 𝔸 𝔹 L) ↔
      (ProjectionClosed F ∧ Finitizable F ∧ ContainsId F) := by sorry

end SymBoolPCSP.PolChar
