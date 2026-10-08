-- Prove2me | Theorems.Thm_SymBoolPCSP_Galois_chain
-- name    : SymBoolPCSP.Galois.chain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:29.467106+00:00
-- url     : https://prove2.me/theorems/53121235-1b06-4345-9510-60b447e64b75
-- title:
--   Proof of Theorem 6.1 — P′ ⊆ S′_m ⊆ T′_m ⊆ Q′
-- statement:
--   Let $D$ be a finite domain, $\Gamma$ a finite family and $\Gamma'$ a family of promise relations on $D$ with $\mathrm{Pol}(\Gamma) \subseteq \mathrm{Pol}(\Gamma')$. Let $(P', Q') \in \Gamma'$ have arity $k$, let $m = |P'|$ and let $x^1, \dots, x^m$ be an ordering of the elements of $P'$. With $y^i_j = x^j_i$ and $S'_m, T'_m$ as in the previous milestone,
--   $$P' \subseteq S'_m \subseteq T'_m \subseteq Q'.$$
--
--   Together with the sandwich remark this makes $(P', Q')$ ppp-definable from $(S'_m, T'_m)$, and then from $\Gamma$ by transitivity.
--
--   **Formalization Note** The ordering of $P'$ is a bijection `e : Fin m ≃ P'`, so $m = |P'|$ is enforced by the bijection; $m = 0$ (empty $P'$) is included. $\mathrm{Pol}(\Gamma) \subseteq \mathrm{Pol}(\Gamma')$ ranges over all arities $L \ge 0$.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, p. 28, proof of Theorem 6.1

import Mathlib
import Definitions.Def_SymBoolPCSP_Galois_Basic

namespace SymBoolPCSP.Galois

open PCSPBLPAff.Symmetric

/-- Proof of Theorem 6.1, p. 28: let `Pol(Γ) ⊆ Pol(Γ′)`, let `(P', Q') = (𝔸'.rel R', 𝔹'.rel R')`
be a relation of `Γ′` with `m = |P'|`, and let `x^1, …, x^m` be an ordering `e` of `P'`. With
`(y_i)_j = (x^j)_i`, `S′_m = {(f(y_1), …, f(y_k)) : f ∈ S_m}` and
`T′_m = {(f(y_1), …, f(y_k)) : f ∈ T_m}`, we have `P' ⊆ S′_m ⊆ T′_m ⊆ Q'`. -/
theorem chain {τ τ' : Type} [Fintype τ] {ar : τ → ℕ} {ar' : τ' → ℕ}
    {D : Type} [Fintype D] [DecidableEq D]
    (𝔸 𝔹 : RelStruct τ ar D) (𝔸' 𝔹' : RelStruct τ' ar' D)
    (hΓ : IsPromiseFamily 𝔸 𝔹) (hΓ' : IsPromiseFamily 𝔸' 𝔹')
    (hPol : PolSubset 𝔸 𝔹 𝔸' 𝔹') (R' : τ') (m : ℕ) (e : Fin m ≃ 𝔸'.rel R') :
    𝔸'.rel R' ⊆ evalAt (fun j => (e j : Fin (ar' R') → D)) (SL 𝔸 m) ∧
      evalAt (fun j => (e j : Fin (ar' R') → D)) (SL 𝔸 m) ⊆
        evalAt (fun j => (e j : Fin (ar' R') → D)) (TL 𝔸 𝔹 m) ∧
      evalAt (fun j => (e j : Fin (ar' R') → D)) (TL 𝔸 𝔹 m) ⊆ 𝔹'.rel R' := by sorry

end SymBoolPCSP.Galois
