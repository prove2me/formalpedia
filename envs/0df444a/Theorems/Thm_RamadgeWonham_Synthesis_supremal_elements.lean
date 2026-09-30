-- Prove2me | Theorems.Thm_RamadgeWonham_Synthesis_supremal_elements
-- name    : RamadgeWonham.Synthesis.supremal_elements
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:42:00.677765+00:00
-- url     : https://prove2.me/theorems/6cfcff24-f051-4342-a74a-106d484fe0ed
-- title:
--   §7, p. 218 — C_𝒢(L), F_𝒢(L) (and C_𝒢(L) ∩ F_𝒢(L)) contain their supremal elements
-- statement:
--   Let $\mathcal G$ be a generator over a finite alphabet with controllable events $\Sigma_c$ and $L(\mathcal G) = \bar L_m(\mathcal G)$, and let $L \subseteq L(\mathcal G)$. Each of the classes
--
--   $$\mathbf C_{\mathcal G}(L), \qquad \mathbf F_{\mathcal G}(L), \qquad \mathbf C_{\mathcal G}(L) \cap \mathbf F_{\mathcal G}(L)$$
--
--   contains a (necessarily unique) greatest element with respect to inclusion, namely the union of all its members; these are denoted $\sup \mathbf C_{\mathcal G}(L)$, $\sup \mathbf F_{\mathcal G}(L)$ and $\sup\{\mathbf C_{\mathcal G}(L) \cap \mathbf F_{\mathcal G}(L)\}$.
--
--   The supremal controllable sublanguage is the central object of the theory: Theorem 7.1 identifies it as the behaviour of the minimally restrictive supervisor.
--
--   **Formalization Note.** $\sup$ is `sSup` in the complete lattice `Set (List α)` (the union of the class), and "contains its supremal element" is `IsGreatest`. The third class is the one Theorem 7.1 (ii) uses; the paper covers it by "In fact, $\mathbf C_{\mathcal G}(L)$ and $\mathbf F_{\mathcal G}(L)$ are complete subsemilattices".
-- source:
--   Ramadge and Wonham, Supervisory Control of a Class of Discrete Event Processes, SIAM J. Control Optim. 25(1), 1987, p. 218, §7, display after the proof of Proposition 7.1

import Mathlib
import Definitions.Def_RamadgeWonham_Synthesis_Controllable

namespace RamadgeWonham.Synthesis

/-- Ramadge–Wonham 1987, §7, p. 218, display after the proof of Proposition 7.1. Standing
assumptions: `Σ` finite (p. 207), `L(𝒢) = L̄_m(𝒢)` (§5, p. 213). For `L ⊆ L(𝒢)`, each of
`C_𝒢(L)`, `F_𝒢(L)` (and `C_𝒢(L) ∩ F_𝒢(L)`, used in Theorem 7.1 (ii)) contains a supremal element
with respect to inclusion, namely its union `sup = sSup`. -/
theorem supremal_elements {α : Type} [Fintype α] (G : Shared.Generator α) (Ec : Set α)
    (hG : G.L = Shared.pre G.Lm) (L : Set (List α)) (hL : L ⊆ G.L) :
    IsGreatest (Cset G Ec L) (sSup (Cset G Ec L)) ∧
      IsGreatest (Fset G L) (sSup (Fset G L)) ∧
      IsGreatest (Cset G Ec L ∩ Fset G L) (sSup (Cset G Ec L ∩ Fset G L)) := by sorry

end RamadgeWonham.Synthesis
