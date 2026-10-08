-- Prove2me | Theorems.Thm_ProjSchedTW_OrderPolyhedra_time_feasible_iff_no_positive_cycle
-- name    : ProjSchedTW.OrderPolyhedra.time_feasible_iff_no_positive_cycle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T15:30:16.980637+00:00
-- url     : https://prove2.me/theorems/d6ca0ef4-049f-4fed-a01d-89078595cade
-- title:
--   Proposition 2.3.3 — a strict order is time-feasible iff its order network has no cycle of positive length
-- statement:
--   Consider a project satisfying the standing assumptions, with activity set $V = \{0, \dots, n+1\}$, project network $N$, and durations $p$. Let $O$ be a strict order in $V$, $\mathcal S_T(O)$ its order polyhedron and $N(O)$ its order network.
--
--   Then
--   $$\mathcal S_T(O) \neq \emptyset \iff N(O) \text{ contains no cycle of positive length.}$$
--
--   This reduces the time-feasibility of a strict order, a question about a polyhedron of schedules, to a question about the weighted network $N(O)$.
--
--   **Formalization Note** The standing assumptions include that $N$ has a path of nonnegative length from $0$ to every node (p. 8); this is the hypothesis under which the book's Theorem 1.3.3 (restated here for $N(O)$) holds, and without it the equivalence fails. Cycles are closed walks with at least one arc.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 31, Proposition 2.3.3

import Mathlib
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Project
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Resources
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Orders

namespace ProjSchedTW.OrderPolyhedra

/-- Proposition 2.3.3 (p. 31): a strict order `O` in `V` is time-feasible if and only if the
order network `N(O)` does not contain a cycle of positive length. -/
theorem time_feasible_iff_no_positive_cycle {n : ℕ} {K : Type} [Fintype K]
    (P : Project n K) (hP : P.StandingAssumptions)
    (O : Finset (Fin (n + 2) × Fin (n + 2))) (hO : IsStrictOrderSet O) :
    P.IsTimeFeasibleOrder O ↔ ¬ (P.orderNetwork O).HasPositiveCycle := by sorry

end ProjSchedTW.OrderPolyhedra
