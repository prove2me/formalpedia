-- Prove2me | Theorems.Thm_ProjSchedTW_NetPresentValue_npv_vertex_optimal_iff_tree_signs
-- name    : ProjSchedTW.NetPresentValue.npv_vertex_optimal_iff_tree_signs
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:44:51.982412+00:00
-- url     : https://prove2.me/theorems/488bf43b-ea50-465f-9ca7-55c964a28507
-- title:
--   Proposition 3.9.2 — a vertex schedule is NPV-optimal iff the subproject net present values of a spanning tree have the right signs
-- statement:
--   Consider a project whose network $N$ has, for every node $i$, a walk from $0$ to $i$ of nonnegative length (the standing convention of §1.2). Let $0<\beta\le1$ be the discount rate, $c_i^F\in\mathbb R$ the cash flows, and $S$ a vertex of the time-feasible region $\mathcal S_T$. For a spanning tree $G=\langle V,E^G\rangle$ associated with $S$ and an arc $\langle i,j\rangle\in E^G$ write
--   $$npv^{ij}(S)=\sum_{h\in V_{ij}}c_h^F\beta^{S_h+p_h},$$
--   where $V_{ij}$ is the part of the tree cut off from node $0$ by deleting $\langle i,j\rangle$.
--
--   1. **Sufficiency.** If some spanning tree $G$ associated with $S$ satisfies $npv^{ij}(S)\ge0$ for every forward arc and $npv^{ij}(S)\le0$ for every backward arc $\langle i,j\rangle\in E^G$, then $S$ is a time-optimal schedule, i.e. it minimizes $f(S)=-\sum_{i\in V}c_i^F\beta^{S_i+p_i}$ over $\mathcal S_T$.
--   2. **Necessity.** If $\beta<1$ and $S$ is time-optimal, then some spanning tree $G$ associated with $S$ satisfies these sign conditions.
--
--   In words: a vertex schedule maximizes the project net present value exactly when no subproject with positive net present value can be started earlier and no subproject with negative net present value can be delayed. This criterion underlies the parametric analysis of the net present value in the discount rate and the deadline (Propositions 3.9.3 and 3.9.4).
--
--   **Formalization Note** The book's "the corresponding spanning tree" is, by the paragraph before the proposition, a tree chosen *using* optimality (one on which the steepest descent direction vanishes); a degenerate vertex has several associated trees, and not all of them need satisfy the sign conditions. The statement is therefore pinned: sufficiency for every associated tree, necessity as existence of one. Necessity is stated for $\beta<1$: at $\beta=1$ the objective is constant, every schedule is optimal, and the sign conditions can fail on every tree. The reachability convention is needed for necessity; without it a vertex may be fixed by $S_i\ge0$ rather than by arcs of $N$.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 333, Proposition 3.9.2 (definitions of forward/backward arcs, V_ij and npv^{ij}(S) on the same page; interpretation p. 334)

import Mathlib
import Definitions.Def_ProjSchedTW_NetPresentValue_Project
import Definitions.Def_ProjSchedTW_NetPresentValue_Trees

namespace ProjSchedTW.NetPresentValue

/-- Proposition 3.9.2 (p. 333), in the pinned reading of "the corresponding spanning tree".
Let `0 < β ≤ 1`, let every node be reached from `0` by a walk of nonnegative length (§1.2, p. 8),
and let `S` be a vertex of the time-feasible region `S_T`.
1. (sufficiency) If `E^G` is any spanning tree of `N` associated with `S` (Proposition 3.2.16)
   such that `npv^{ij}(S) ≥ 0` for every forward arc and `npv^{ij}(S) ≤ 0` for every backward arc
   `⟨i, j⟩ ∈ E^G`, then `S` is time-optimal for `PS∞|temp, d̄| −∑ c_i^F β^{C_i}`.
2. (necessity, `β < 1`) If `S` is time-optimal, then some spanning tree associated with `S`
   satisfies these sign conditions. -/
theorem npv_vertex_optimal_iff_tree_signs {n : ℕ} (P : Project n) (β : ℝ) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) (c : Fin (n + 2) → ℝ)
    (hreach : ∀ i : Fin (n + 2), ∃ w : ℤ, 0 ≤ w ∧ WalkLength P 0 i w)
    (S : Fin (n + 2) → ℝ) (hS : S ∈ (timeFeasibleSet P).extremePoints ℝ) :
    (∀ EG : Finset (Fin (n + 2) × Fin (n + 2)), IsAssociatedTree P EG S →
      TreeSignCondition P β c EG S → IsTimeOptimal P β c S) ∧
    (β < 1 → IsTimeOptimal P β c S →
      ∃ EG : Finset (Fin (n + 2) × Fin (n + 2)), IsAssociatedTree P EG S ∧
        TreeSignCondition P β c EG S) := by sorry

end ProjSchedTW.NetPresentValue
