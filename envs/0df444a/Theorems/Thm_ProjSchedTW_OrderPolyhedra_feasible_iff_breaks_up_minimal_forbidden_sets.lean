-- Prove2me | Theorems.Thm_ProjSchedTW_OrderPolyhedra_feasible_iff_breaks_up_minimal_forbidden_sets
-- name    : ProjSchedTW.OrderPolyhedra.feasible_iff_breaks_up_minimal_forbidden_sets
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T15:30:45.898744+00:00
-- url     : https://prove2.me/theorems/56a64c25-3085-4ec3-bf21-ec0a9ae19de7
-- title:
--   Theorem 2.3.10 — a time-feasible strict order is feasible iff its order network separates every minimal forbidden set
-- statement:
--   Consider a project satisfying the standing assumptions, with durations $p$, project network $N$ and set $\mathcal F$ of minimal forbidden sets. Let $O$ be a time-feasible strict order in $V$ and $N(O)$ its order network. Then $O$ is feasible, i.e. every schedule of the order polyhedron $\mathcal S_T(O)$ is resource-feasible, if and only if
--
--   $$\forall F \in \mathcal F\ \ \exists\, i, j \in F:\ N(O) \text{ contains a path from } i \text{ to } j \text{ of length at least } p_i.$$
--
--   This theorem of Bartusch, Möhring & Radermacher (1988) makes the feasibility of a strict order checkable by longest-path computations in $N(O)$, complementing Proposition 2.3.3, which does the same for time-feasibility. It underlies the branch-and-bound schemes of the chapter that resolve resource conflicts by adding precedence pairs.
--
--   **Formalization Note** Resource constraints are required for every $t \ge 0$. Paths are walks; since $O$ is time-feasible, $N(O)$ has no cycle of positive length, so this agrees with the book's paths and longest path lengths. Every minimal forbidden set consists of real activities (because $r_{0k} = r_{n+1,k} = 0$), whose durations are positive, so the trivial path from $i$ to itself never qualifies.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 35, Theorem 2.3.10

import Mathlib
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Project
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Resources
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Orders

namespace ProjSchedTW.OrderPolyhedra

/-- Theorem 2.3.10 (p. 35, Bartusch et al. 1988): a time-feasible strict order `O` in `V` is
feasible if and only if for each minimal forbidden set `F ∈ ℱ`, the order network `N(O)`
contains a path from some node `i ∈ F` to some node `j ∈ F` whose length is at least `p_i`. -/
theorem feasible_iff_breaks_up_minimal_forbidden_sets {n : ℕ} {K : Type} [Fintype K]
    (P : Project n K) (hP : P.StandingAssumptions)
    (O : Finset (Fin (n + 2) × Fin (n + 2))) (hO : P.IsTimeFeasibleOrder O) :
    P.IsFeasibleOrder O ↔
      ∀ F : Finset (Fin (n + 2)), P.IsMinimalForbidden F →
        ∃ i ∈ F, ∃ j ∈ F, (P.orderNetwork O).HasPathOfLengthAtLeast i j (P.p i) := by sorry

end ProjSchedTW.OrderPolyhedra
