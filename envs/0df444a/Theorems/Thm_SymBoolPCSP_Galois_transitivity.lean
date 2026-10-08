-- Prove2me | Theorems.Thm_SymBoolPCSP_Galois_transitivity
-- name    : SymBoolPCSP.Galois.transitivity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:18.371236+00:00
-- url     : https://prove2.me/theorems/af033018-46ea-45a3-9a75-ce1c48488738
-- title:
--   §6.1 remark — ppp-definability is transitive
-- statement:
--   Let $D$ be a finite domain, let $\Gamma$ and $\Gamma'$ be finite families of promise relations on $D$, and suppose that $\Gamma'$ is ppp-definable from $\Gamma$, i.e. every promise relation of $\Gamma'$ is ppp-definable from $\Gamma$. If a promise relation $(P'', Q'')$ (with $P'' \subseteq Q''$) is ppp-definable from $\Gamma'$, then
--   $$(P'', Q'') \text{ is ppp-definable from } \Gamma.$$
--
--   Equivalently: if $\Gamma'$ is ppp-definable from $\Gamma$ and $\Gamma''$ is ppp-definable from $\Gamma'$, then $\Gamma''$ is ppp-definable from $\Gamma$. This is what lets the proof of Theorem 6.1 chain the definitions of $(S_m, T_m)$ from $\Gamma$, of $(S'_m, T'_m)$ from $(S_m, T_m)$, and of $(P', Q')$ from $(S'_m, T'_m)$.
--
--   **Formalization Note** The family-level statement of the paper is stated relation by relation for $\Gamma''$, which is equivalent. $\Gamma$ and $\Gamma'$ are pairs of structures with finite signatures (`[Fintype τ]`, `[Fintype τ']`), as Definition 6.2 asks for finite families.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, p. 27, §6.1, remark after Definition 6.2

import Mathlib
import Definitions.Def_SymBoolPCSP_Galois_Basic

namespace SymBoolPCSP.Galois

open PCSPBLPAff.Symmetric

/-- §6.1, p. 27 (after Definition 6.2), transitivity of ppp-definability: if every relation of
the finite family `Γ′ = (𝔸', 𝔹')` is ppp-definable from the finite family `Γ = (𝔸, 𝔹)`, and
`(P'', Q'')` is ppp-definable from `Γ′`, then `(P'', Q'')` is ppp-definable from `Γ`. -/
theorem transitivity {τ τ' : Type} [Fintype τ] [Fintype τ'] {ar : τ → ℕ} {ar' : τ' → ℕ}
    {D : Type} [Fintype D] [DecidableEq D]
    (𝔸 𝔹 : RelStruct τ ar D) (𝔸' 𝔹' : RelStruct τ' ar' D)
    (hΓ : IsPromiseFamily 𝔸 𝔹) (hΓ' : IsPromiseFamily 𝔸' 𝔹')
    (hΓ'Γ : ∀ R' : τ', PPPDefinable 𝔸 𝔹 (𝔸'.rel R') (𝔹'.rel R'))
    {k : ℕ} (P'' Q'' : Set (Fin k → D)) (hPQ'' : P'' ⊆ Q'')
    (hΓ''Γ' : PPPDefinable 𝔸' 𝔹' P'' Q'') :
    PPPDefinable 𝔸 𝔹 P'' Q'' := by sorry

end SymBoolPCSP.Galois
