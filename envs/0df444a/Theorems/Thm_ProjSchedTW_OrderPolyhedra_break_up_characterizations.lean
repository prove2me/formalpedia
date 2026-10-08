-- Prove2me | Theorems.Thm_ProjSchedTW_OrderPolyhedra_break_up_characterizations
-- name    : ProjSchedTW.OrderPolyhedra.break_up_characterizations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T15:30:34.664009+00:00
-- url     : https://prove2.me/theorems/41933ac9-b07c-4722-ac5c-c83d8de7d9be
-- title:
--   Remark 2.3.11 — partitions, breaking up forbidden sets, and feasibility
-- statement:
--   Consider a project satisfying the standing assumptions.
--
--   1. A time-feasible schedule $S$ partitions a set $F \subseteq V$ if and only if $\mathcal A(S,t) \cap F$ is a feasible (not forbidden) set for every $t \ge 0$.
--   2. A time-feasible strict order $O$ is feasible if and only if $O$ breaks up every forbidden set; and $O$ breaks up every forbidden set if and only if it breaks up every minimal forbidden set.
--   3. A time-feasible schedule $S$ is feasible if and only if $S$ partitions every forbidden set.
--
--   In symbols, for time-feasible $S$ and $O$:
--   $$S \text{ partitions } F \iff \forall t \ge 0:\ \mathcal A(S,t) \cap F \text{ is feasible},\qquad O \text{ feasible} \iff O \text{ breaks up all } F \text{ forbidden}.$$
--
--   The remark translates the resource conditions into the language of breaking up forbidden sets, used by the branch-and-bound methods of the chapter.
--
--   **Formalization Note** Resource constraints use every $t \ge 0$. "Breaks up" is stated with "some path of length $\ge p_i$" in $N(O)$, which for time-feasible $O$ equals the book's longest-path formulation.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 36, Remark 2.3.11

import Mathlib
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Project
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Resources
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Orders

namespace ProjSchedTW.OrderPolyhedra

/-- Remark 2.3.11 (p. 36):
1. a time-feasible schedule `S` partitions a set `F` if and only if for all `t ≥ 0` the set
   `A(S,t) ∩ F` is feasible (not forbidden);
2. a time-feasible strict order `O` is feasible if and only if `O` breaks up all forbidden sets,
   which holds precisely if `O` breaks up all minimal forbidden sets;
3. a time-feasible schedule `S` is feasible if and only if `S` partitions all forbidden sets. -/
theorem break_up_characterizations {n : ℕ} {K : Type} [Fintype K]
    (P : Project n K) (hP : P.StandingAssumptions) :
    (∀ S : Fin (n + 2) → ℝ, P.IsTimeFeasible S → ∀ F : Finset (Fin (n + 2)),
      P.Partitions S F ↔ ∀ t : ℝ, 0 ≤ t → ¬ P.IsForbidden (P.activeSet S t ∩ F)) ∧
    (∀ O : Finset (Fin (n + 2) × Fin (n + 2)), P.IsTimeFeasibleOrder O →
      (P.IsFeasibleOrder O ↔
          ∀ F : Finset (Fin (n + 2)), P.IsForbidden F → P.BreaksUp O F) ∧
      ((∀ F : Finset (Fin (n + 2)), P.IsForbidden F → P.BreaksUp O F) ↔
          ∀ F : Finset (Fin (n + 2)), P.IsMinimalForbidden F → P.BreaksUp O F)) ∧
    (∀ S : Fin (n + 2) → ℝ, P.IsTimeFeasible S →
      (P.IsFeasible S ↔ ∀ F : Finset (Fin (n + 2)), P.IsForbidden F → P.Partitions S F)) := by sorry

end ProjSchedTW.OrderPolyhedra
