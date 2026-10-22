-- Prove2me | Theorems.Thm_ThinFlowSP_Breakpoints_theorem_31
-- name    : ThinFlowSP.Breakpoints.theorem_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:30:13.569403+00:00
-- url     : https://prove2.me/theorems/d7beff93-7218-42b2-aab4-c4303b37e1c5
-- title:
--   Theorem 31, p. 20 — the thin-flow label function of a two-terminal series-parallel network has at most 2|A′| − |A*| − |V| + 1 breakpoints
-- statement:
--   Let $G' = (V, A')$ be a two-terminal series-parallel directed multigraph, $A^* \subseteq A'$ a set of resetting arcs and $\nu \in \mathbb R^{A'}_{>0}$ capacities. Then the label function $\varrho^{G'}$ exists: for every flow value $\nu'_0 \ge 0$, $\varrho^{G'}(\nu'_0)$ are the corresponding labels, with label $1$ at $s$, of a normalized thin $s$–$t$-flow with resetting of value $\nu'_0$. Moreover $\varrho^{G'}$ is continuous on $[0,\infty)$, has finitely many breakpoints in $(0,\infty)$, and
--   $$\#\{\text{breakpoints of } \varrho^{G'}\} \le 2|A'| - |A^*| - |V| + 1 .$$
--
--   The bound makes the recursive computation of $\varrho^{G'}$ along a series-parallel decomposition output-polynomial; for a single arc it is attained ($1$ breakpoint at $\nu_a$ if $a \notin A^*$, none if $a \in A^*$).
--
--   **Formalization Note** Series-parallel multigraphs are the graphs of terms built from a single arc by series and parallel composition (Definition 28); every member of the class is isomorphic to such a graph and all quantities are isomorphism-invariant. The statement bounds every function with the defining property of $\varrho^{G'}$ (unique on $[0,\infty)$ by Corollary 15) and asserts that one exists, so it is not vacuous. Continuity is taken from Proposition 17 and makes "finitely many breakpoints" mean "finitely many affine pieces". A breakpoint is a point $\nu'_0 > 0$ near which some component is not affine. The arithmetic is in $\mathbb Z$. The second clause of the theorem, "can be computed in polynomial time", is not formalized.
-- source:
--   Kaiser, Computation of Dynamic Equilibria in Series-Parallel Networks, arXiv:2002.11428v2, p. 20, Theorem 31

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Model

namespace ThinFlowSP.Breakpoints

theorem theorem_31 (T : SPTerm) (Astar : Finset T.toNet.A) (ν : T.toNet.A → ℝ)
    (hν : ∀ a, 0 < ν a) :
    (∃ ρ : ℝ → T.toNet.V → ℝ, IsLabelFunction T.toNet Astar ν ρ) ∧
    ∀ ρ : ℝ → T.toNet.V → ℝ, IsLabelFunction T.toNet Astar ν ρ →
      ContinuousOn ρ (Set.Ici 0) ∧ (breakpoints ρ).Finite ∧
      ((breakpoints ρ).ncard : ℤ) ≤
        2 * (Fintype.card T.toNet.A : ℤ) - (Astar.card : ℤ) - (Fintype.card T.toNet.V : ℤ) + 1 := by sorry

end ThinFlowSP.Breakpoints
