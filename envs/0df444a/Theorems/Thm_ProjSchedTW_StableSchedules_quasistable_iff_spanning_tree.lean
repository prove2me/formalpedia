-- Prove2me | Theorems.Thm_ProjSchedTW_StableSchedules_quasistable_iff_spanning_tree
-- name    : ProjSchedTW.StableSchedules.quasistable_iff_spanning_tree
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T01:16:23.419861+00:00
-- url     : https://prove2.me/theorems/0b6aef6c-6c00-47a5-a76d-a1862febe792
-- title:
--   Theorem 3.2.18 — quasistable schedules are the spanning-tree solutions of their schedule network
-- statement:
--   Let $S$ be a feasible schedule. Then $S$ is quasistable if and only if there is a spanning tree $G=\langle V,E^G;\delta^G\rangle$ of the schedule network $N(O(S))$ such that $S$ is the unique solution of
--   $$S_0=0,\qquad S_j-S_i=\delta^G_{ij}\quad(\langle i,j\rangle\in E^G).$$
--   Here the arcs of $G$ are arcs of $N(O(S))$, and $\delta^G_{ij}$ is the weight of $\langle i,j\rangle$ in $N(O(S))$ (Definition 2.3.2): $\delta_{ij}$ for a temporal constraint, $p_i$ for a precedence constraint of $O(S)$, and $\max(\delta_{ij},p_i)$ for an arc that is both. If $S$ is quasiactive, $G$ can be chosen to be a spanning outtree of $N(O(S))$ rooted at $0$.
--
--   The theorem turns the shift-based definition of quasistability into a finite combinatorial certificate. Remark 3.2.7 and the integrality of quasistable schedules follow from it.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 218, Theorem 3.2.18 and the note after it

import Mathlib
import Definitions.Def_ProjSchedTW_StableSchedules_Project
import Definitions.Def_ProjSchedTW_StableSchedules_Shifts
import Definitions.Def_ProjSchedTW_StableSchedules_Trees

namespace ProjSchedTW.StableSchedules

/-- Theorem 3.2.18 (p. 218). A feasible schedule `S` is quasistable iff there is a spanning tree
`E^G` of the schedule network `N(O(S))` (arcs of `N(O(S))`, weights of Definition 2.3.2) such
that `S` uniquely solves `S_0 = 0`, `S_j − S_i = δ^G_ij` (`⟨i,j⟩ ∈ E^G`). If `S` is quasiactive,
the tree can be chosen to be a spanning outtree of `N(O(S))` rooted at `0`. -/
theorem quasistable_iff_spanning_tree {n : ℕ} {K : Type} (P : Project n K)
    (S : Fin (n + 2) → ℝ) (hS : S ∈ feasibleSet P) :
    (IsQuasistable P S ↔
      ∃ EG : Finset (Fin (n + 2) × Fin (n + 2)),
        (∀ e ∈ EG, e ∈ orderArcs P (scheduleOrder P S)) ∧ IsSpanningTree EG ∧
        UniquelySolves (orderWeight P (scheduleOrder P S)) EG S) ∧
    (IsQuasiactive P S →
      ∃ EG : Finset (Fin (n + 2) × Fin (n + 2)),
        (∀ e ∈ EG, e ∈ orderArcs P (scheduleOrder P S)) ∧ IsSpanningOuttree 0 EG ∧
        UniquelySolves (orderWeight P (scheduleOrder P S)) EG S) := by sorry

end ProjSchedTW.StableSchedules
