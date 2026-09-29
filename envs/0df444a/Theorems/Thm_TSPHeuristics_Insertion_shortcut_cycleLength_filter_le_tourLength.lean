-- Prove2me | Theorems.Thm_TSPHeuristics_Insertion_shortcut_cycleLength_filter_le_tourLength
-- name    : TSPHeuristics.Insertion.shortcut_cycleLength_filter_le_tourLength
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:31:32.126592+00:00
-- url     : https://prove2.me/theorems/67602732-3ebd-47d9-b083-afa048dcc1f7
-- title:
--   Eq. (2.2) — shortcutting a tour to a subset of the nodes does not increase its length
-- statement:
--   Let $(N,d)$ be a traveling salesman graph with $n$ nodes, let $\tau$ be a tour visiting $\tau(0),\dots,\tau(n-1)$, and let $H\subseteq N$ be any set of nodes. Let $T_H$ be the tour on $H$ that visits the nodes of $H$ in the same order as $\tau$ does. Then
--   $$\mathrm{cyc}_d(T_H)\le \mathrm{len}_d(\tau).$$
--   In particular, taking $\tau$ optimal gives the paper's (2.2), $\mathrm{OPTIMAL}\ge\mathrm{LENGTH}$.
--
--   This is the shortcutting step in the proof of Lemma 1: each edge $(b,c)$ of $T_H$ is no longer than the stretch of $\tau$ from $b$ to $c$.
--
--   **Formalization Note** Nodes are `Fin n` (0-based). A traveling salesman graph is `IsTSPDist d`: symmetric, nonnegative, triangle inequality, plus the normalization $d(i,i)=0$, which is not in the paper and does not affect any length, since a loop never enters a tour, subtour or insertion cost. The paper uses a particular $H$, the $\min(2k,n)$ nodes with the largest numbers $l_i$; the statement is given for every $H$, which is what the argument proves. For $H=\emptyset$ the left side is $0$.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, https://doi.org/10.1137/0206041, p. 565, proof of Lemma 1, eq. (2.2)

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_Insertion_InsertionMethod

namespace TSPHeuristics.Insertion

/-- (2.2), p. 565, in the general form the argument proves: visiting any subset `H` of the
nodes in the order in which a tour `τ` visits them gives a closed tour on `H` no longer than `τ`
(the triangle inequality shortcuts the skipped nodes). -/
theorem shortcut_cycleLength_filter_le_tourLength {n : ℕ} (d : Fin n → Fin n → ℝ)
    (hd : TSPHeuristics.Shared.IsTSPDist d) (τ : Equiv.Perm (Fin n)) (H : Finset (Fin n)) :
    TSPHeuristics.Shared.cycleLength d ((List.ofFn τ).filter (fun i => decide (i ∈ H))) ≤ TSPHeuristics.Shared.tourLength d τ := by sorry

end TSPHeuristics.Insertion
