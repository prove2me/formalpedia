-- Prove2me | Theorems.Thm_ProjSchedTW_Cumulative_inventoryFeasible_iff_resolves_minimal_sets
-- name    : ProjSchedTW.Cumulative.inventoryFeasible_iff_resolves_minimal_sets
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T00:02:24.376493+00:00
-- url     : https://prove2.me/theorems/afbb6247-5328-4ecb-8f93-a084f913fe46
-- title:
--   Theorem 2.12.4 — a schedule is inventory-feasible iff it resolves every minimal surplus and shortage set
-- statement:
--   Consider a project with activities $V=\{0,\dots,n+1\}$, durations $p_i$ and discrete cumulative resources $k\in\mathcal R^\gamma$ with integer demands $r_{ik}$, safety stocks $\underline R_k$ and storage capacities $\overline R_k$ (§2.12.1). Assume (2.12.1), $\underline R_k\le\sum_{i\in V}r_{ik}\le\overline R_k$, and Remark 2.12.2, $\underline R_k\le 0\le\overline R_k$, for every $k$. Let $\mathcal F_k^+$ and $\mathcal F_k^-$ be the sets of minimal $k$-surplus and minimal $k$-shortage sets. Then a schedule $S$ is inventory-feasible, i.e. $\underline R_k\le r_k(S,t)\le\overline R_k$ for all $k$ and all $t\ge 0$, if and only if
--
--   1. for each $F\in\mathcal F_k^+$ with $k\in\mathcal R^\gamma$ there exist $j\in F$ and $i\notin F$ with $r_{jk}>0$ and $r_{ik}<0$ such that
--   $$S_j+p_j\ge S_i,$$
--   2. for each $F\in\mathcal F_k^-$ with $k\in\mathcal R^\gamma$ there exist $j\in F$ and $i\notin F$ with $r_{jk}<0$ and $r_{ik}>0$ such that
--   $$S_j\ge S_i+p_i.$$
--
--   The theorem says that every inventory conflict can be resolved by adding start-to-completion or completion-to-start precedence constraints to the temporal constraints, so that the feasible region of the problem with cumulative resources is a finite union of polyhedra; it underlies the branch-and-bound procedure of Neumann and Schwindt (2002).
--
--   **Formalization Note** The inventory constraints (2.12.2) are required for every $t\ge 0$ rather than for $0\le t\le\bar d$ as printed; the book's proof uses arbitrary $t\ge 0$. Schedules satisfy $S_0=0$, $S_i\ge 0$ but need not be time-feasible, as in the book's statement.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, pp. 132–134, Theorem 2.12.4

import Mathlib
import Definitions.Def_ProjSchedTW_Cumulative_Model

namespace ProjSchedTW.Cumulative

/-- Theorem 2.12.4. -/
theorem inventoryFeasible_iff_resolves_minimal_sets {n : ℕ} {K : Type}
    (P : CumulativeProject n K)
    (h2121 : TotalDemandWithinBounds P) (hRem : BoundsStraddleZero P)
    (S : Fin (n + 2) → ℝ) (hS : IsSchedule S) :
    InventoryFeasible P S ↔ ResolvesSurplusSets P S ∧ ResolvesShortageSets P S := by sorry

end ProjSchedTW.Cumulative
