-- Prove2me | Theorems.Thm_RamadgeWonham_Synthesis_prop_7_1
-- name    : RamadgeWonham.Synthesis.prop_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:41:33.055346+00:00
-- url     : https://prove2.me/theorems/a992179e-f345-4a2d-8535-84f37f8f0117
-- title:
--   Proposition 7.1, p. 218 — C_𝒢(L) and F_𝒢(L) are nonempty and closed under arbitrary unions
-- statement:
--   Let $\mathcal G$ be a generator over a finite alphabet with controllable events $\Sigma_c$ and $L(\mathcal G) = \bar L_m(\mathcal G)$, and let $L \subseteq L(\mathcal G)$. The class $\mathbf C_{\mathcal G}(L)$ of controllable sublanguages of $L$ and the class $\mathbf F_{\mathcal G}(L)$ of $L_m(\mathcal G)$-closed sublanguages of $L$ are nonempty, both containing the empty language, and closed under arbitrary unions: for any family $(K_i)_{i \in A}$,
--
--   $$K_i \in \mathbf C_{\mathcal G}(L)\ \forall i \ \Longrightarrow\ \bigcup_{i \in A} K_i \in \mathbf C_{\mathcal G}(L), \qquad K_i \in \mathbf F_{\mathcal G}(L)\ \forall i \ \Longrightarrow\ \bigcup_{i \in A} K_i \in \mathbf F_{\mathcal G}(L).$$
--
--   This lattice property is what makes minimally restrictive supervision possible.
--
--   **Formalization Note.** "Nonempty class" is stated in the stronger form $\emptyset \in \mathbf C_{\mathcal G}(L)$, $\emptyset \in \mathbf F_{\mathcal G}(L)$, which is how the paper proves it. Families are subsets `𝒦` of the class and the union is `⋃₀ 𝒦`.
-- source:
--   Ramadge and Wonham, Supervisory Control of a Class of Discrete Event Processes, SIAM J. Control Optim. 25(1), 1987, p. 218, Proposition 7.1

import Mathlib
import Definitions.Def_RamadgeWonham_Synthesis_Controllable

namespace RamadgeWonham.Synthesis

/-- Ramadge–Wonham 1987, Proposition 7.1, p. 218. Standing assumptions: `Σ` finite (p. 207),
`L(𝒢) = L̄_m(𝒢)` (§5, p. 213). For `L ⊆ L(𝒢)`, the classes `C_𝒢(L)` and `F_𝒢(L)` are nonempty
(both contain `∅`) and closed under arbitrary unions. -/
theorem prop_7_1 {α : Type} [Fintype α] (G : Shared.Generator α) (Ec : Set α)
    (hG : G.L = Shared.pre G.Lm) (L : Set (List α)) (hL : L ⊆ G.L) :
    (∅ ∈ Cset G Ec L ∧ ∀ 𝒦 ⊆ Cset G Ec L, ⋃₀ 𝒦 ∈ Cset G Ec L) ∧
      (∅ ∈ Fset G L ∧ ∀ 𝒦 ⊆ Fset G L, ⋃₀ 𝒦 ∈ Fset G L) := by sorry

end RamadgeWonham.Synthesis
