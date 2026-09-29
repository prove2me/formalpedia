-- Prove2me | Theorems.Thm_TSPHeuristics_NNLower_shortest_paths_F_succ
-- name    : TSPHeuristics.NNLower.shortest_paths_F_succ
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T00:26:12.877659+00:00
-- url     : https://prove2.me/theorems/7cc6a908-23f7-4986-8406-e3255b9c89b4
-- title:
--   Eqs. (2.13)–(2.17): shortest paths between the named nodes of $F_{i+1}$
-- statement:
--   Let $i\ge1$ and let $A,B,C,D,E,F,G$ be the nodes of $F_{i+1}$ named in Fig. 1: $A$, $B$, $C$ the start, middle and right node of the left copy of $F_i$, $D$ the new middle node, and $E$, $F$, $G$ the start, middle and right node of the right copy. Write $\overline{XY}$ for the length of a shortest path between $X$ and $Y$ in $F_{i+1}$. Then
--   $$\begin{aligned}
--   &(2.13)\quad \overline{AB}=\overline{BC}=\overline{EF}=\overline{FG}=l_i-1,\\
--   &(2.14)\quad \overline{AC}=\overline{EG}=l_{i+1}-2,\\
--   &(2.15)\quad \overline{BE}=\overline{DF}=l_i,\\
--   &(2.16)\quad \overline{AD}=\overline{DG}=l_{i+1}-1,\\
--   &(2.17)\quad \overline{AG}=l_{i+2}-2.
--   \end{aligned}$$
--
--   These identities are the induction that establishes properties a) and b) of $\bar G_i$.
--
--   **Formalization Note** With $s=2^{i+1}-1$ the number of nodes of $F_i$: $A=0$, $B=2^i-1$, $C=s-1$, $D=s$, $E=s+1$, $F=s+2^i$, $G=2s$. Distances are taken in $F_{i+1}$ (not $G_{i+1}$).
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, https://doi.org/10.1137/0206041, p. 569, eqs. (2.13)–(2.17)

import Mathlib
import Definitions.Def_TSPHeuristics_NNLower_ShortestPathMetric
import Definitions.Def_TSPHeuristics_NNLower_LowerBoundFamily

namespace TSPHeuristics.NNLower

/-- Eqs. (2.13)–(2.17), p. 569: in `F_{i+1}` (for `i ≥ 1`), with the nodes of Fig. 1
`A = 0`, `B = middle i`, `C = s − 1`, `D = s`, `E = s + 1`, `F = s + 1 + middle i`, `G = 2 s`
(`s = numNodes i`), the shortest-path distances are
`AB = BC = EF = FG = l_i − 1`, `AC = EG = l_{i+1} − 2`, `BE = DF = l_i`,
`AD = DG = l_{i+1} − 1`, `AG = l_{i+2} − 2`. -/
theorem shortest_paths_F_succ (i : ℕ) (hi : 1 ≤ i) :
    let s := numNodes i
    let A := 0
    let B := middle i
    let C := s - 1
    let D := s
    let E := s + 1
    let F := s + 1 + middle i
    let G := 2 * s
    let dF := spDist (edgesF (i + 1))
    (dF A B = ell i - 1 ∧ dF B C = ell i - 1 ∧ dF E F = ell i - 1 ∧ dF F G = ell i - 1) ∧
    (dF A C = ell (i + 1) - 2 ∧ dF E G = ell (i + 1) - 2) ∧
    (dF B E = ell i ∧ dF D F = ell i) ∧
    (dF A D = ell (i + 1) - 1 ∧ dF D G = ell (i + 1) - 1) ∧
    dF A G = ell (i + 2) - 2 := by sorry

end TSPHeuristics.NNLower
