-- Prove2me | Theorems.Thm_SymBoolPCSP_Galois_theorem_6_1_ppp
-- name    : SymBoolPCSP.Galois.theorem_6_1_ppp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:27.670592+00:00
-- url     : https://prove2.me/theorems/f9beca41-4b05-4a8e-89f6-5bc0327e7e6f
-- title:
--   Theorem 6.1 (algebraic core) — Pol(Γ) ⊆ Pol(Γ′) makes every relation of Γ′ ppp-definable from Γ
-- statement:
--   Let $D$ be a finite domain, let $\Gamma$ be a finite family of promise relations on $D$ and $\Gamma'$ a family of promise relations on $D$. If
--   $$\mathrm{Pol}(\Gamma) \subseteq \mathrm{Pol}(\Gamma'),$$
--   then every promise relation $(P', Q') \in \Gamma'$ is ppp-definable from $\Gamma$: there are $\ell \ge 0$ and a $\Gamma \cup \{\mathrm{EQUAL}\}$-PCSP $\Psi$ on $k + \ell$ variables ($k$ the arity of $(P', Q')$) such that every $x \in P'$ extends to an assignment satisfying $\Psi_P$, and every assignment satisfying $\Psi_Q$ restricts on its first $k$ variables to an element of $Q'$.
--
--   This is the promise analogue of the Galois correspondence between clones and relational clones for ordinary CSPs. The printed Theorem 6.1 concludes that there is a polynomial-time reduction from $\mathrm{PCSP}(\Gamma')$ to $\mathrm{PCSP}(\Gamma)$; its proof derives that reduction from the ppp-definability stated here, by replacing every clause of $\Gamma'$ with its gadget.
--
--   **Formalization Note** The polynomial-time reduction is not formalized; this is the algebraic statement the proof establishes ("it suffices to show that every promise relation $(P', Q') \in \Gamma'$ is ppp-definable from $\Gamma$"). $\mathrm{Pol}(\Gamma) \subseteq \mathrm{Pol}(\Gamma')$ ranges over all arities $L \ge 0$, nullary (constant) functions included; restricted to $L \ge 1$ the statement would be false ($\Gamma = \{(D, D)\}$, $\Gamma' = \{(\emptyset, \emptyset)\}$, both unary). No assumption $P' \ne \emptyset$ is made. $\Gamma$ is finite (`[Fintype τ]`); $\Gamma'$ may be infinite, since the conclusion is stated per relation.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, p. 27, Theorem 6.1 (proof p. 28)

import Mathlib
import Definitions.Def_SymBoolPCSP_Galois_Basic

namespace SymBoolPCSP.Galois

open PCSPBLPAff.Symmetric

/-- **Theorem 6.1, algebraic core** (p. 27; proof p. 28). Let `Γ = (𝔸, 𝔹)` be a finite family and
`Γ′ = (𝔸', 𝔹')` a family of promise relations over the finite domain `D` such that
`Pol(Γ) ⊆ Pol(Γ′)` (polymorphisms of every arity `L ≥ 0`). Then every promise relation
`(P', Q') ∈ Γ′` is ppp-definable from `Γ`. (The printed theorem concludes a polynomial-time
reduction from `PCSP(Γ′)` to `PCSP(Γ)`; that complexity statement is not formalized.) -/
theorem theorem_6_1_ppp {τ τ' : Type} [Fintype τ] {ar : τ → ℕ} {ar' : τ' → ℕ}
    {D : Type} [Fintype D] [DecidableEq D]
    (𝔸 𝔹 : RelStruct τ ar D) (𝔸' 𝔹' : RelStruct τ' ar' D)
    (hΓ : IsPromiseFamily 𝔸 𝔹) (hΓ' : IsPromiseFamily 𝔸' 𝔹')
    (hPol : PolSubset 𝔸 𝔹 𝔸' 𝔹') :
    ∀ R' : τ', PPPDefinable 𝔸 𝔹 (𝔸'.rel R') (𝔹'.rel R') := by sorry

end SymBoolPCSP.Galois
