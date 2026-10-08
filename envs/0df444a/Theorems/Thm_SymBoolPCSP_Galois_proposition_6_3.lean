-- Prove2me | Theorems.Thm_SymBoolPCSP_Galois_proposition_6_3
-- name    : SymBoolPCSP.Galois.proposition_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:11.70806+00:00
-- url     : https://prove2.me/theorems/ea6c39bb-77f6-4dc1-8d46-cd4c00a35cc6
-- title:
--   Proposition 6.3 — the promise relation (S_L, T_L) of polymorphisms is ppp-definable from Γ
-- statement:
--   Let $D$ be a finite domain, let $\Gamma = \{(P_R, Q_R)\}$ be a finite family of promise relations on $D$, and let $L$ be a positive integer. Let
--   $$S_L = \{f : D^L \to D : f \in \mathrm{Pol}(P, P) \text{ for all } (P, Q) \in \Gamma\}, \qquad T_L = \{f : D^L \to D : f \in \mathrm{Pol}(P, Q) \text{ for all } (P, Q) \in \Gamma\},$$
--   where a function $f : D^L \to D$ is identified with the vector of its $|D|^L$ values. Then the promise relation $S_L \subseteq T_L \subseteq D^{D^L}$ is ppp-definable from $\Gamma$.
--
--   The proposition says that "being a polymorphism" is itself expressible by a gadget built from $\Gamma$; it is the first step of the proof of the Galois correspondence (Theorem 6.1).
--
--   **Formalization Note** The $|D|^L$ coordinates are ordered by an arbitrary bijection `e : Fin (Fintype.card (Fin L → D)) ≃ (Fin L → D)`, and the statement holds for every such ordering. The hypothesis $L > 0$ is the paper's; the same statement also holds for $L = 0$, which the proof of Theorem 6.1 needs when $P' = \emptyset$.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, p. 28, Proposition 6.3

import Mathlib
import Definitions.Def_SymBoolPCSP_Galois_Basic

namespace SymBoolPCSP.Galois

open PCSPBLPAff.Symmetric

/-- **Proposition 6.3** (p. 28). Let `L` be a positive integer. For a finite family
`Γ = (𝔸, 𝔹)` of promise relations over the finite domain `D`, the promise relation
`S_L ⊆ T_L ⊆ D^{D^L}`, with `S_L = {f : f ∈ Pol(P, P) ∀ (P, Q) ∈ Γ}` and
`T_L = {f : f ∈ Pol(P, Q) ∀ (P, Q) ∈ Γ}`, is ppp-definable from `Γ`, where a function
`f : D^L → D` is identified with the vector of its `|D|^L` values, listed in any order `e`. -/
theorem proposition_6_3 {τ : Type} [Fintype τ] {ar : τ → ℕ} {D : Type} [Fintype D]
    [DecidableEq D] (𝔸 𝔹 : RelStruct τ ar D) (hΓ : IsPromiseFamily 𝔸 𝔹)
    (L : ℕ) (hL : 0 < L) (e : Fin (Fintype.card (Fin L → D)) ≃ (Fin L → D)) :
    PPPDefinable 𝔸 𝔹 (asTuples e (SL 𝔸 L)) (asTuples e (TL 𝔸 𝔹 L)) := by sorry

end SymBoolPCSP.Galois
