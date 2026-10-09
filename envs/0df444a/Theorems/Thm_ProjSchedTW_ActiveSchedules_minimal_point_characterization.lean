-- Prove2me | Theorems.Thm_ProjSchedTW_ActiveSchedules_minimal_point_characterization
-- name    : ProjSchedTW.ActiveSchedules.minimal_point_characterization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T16:05:39.300258+00:00
-- url     : https://prove2.me/theorems/8a11fa8f-98a7-4def-80e3-215f93a954b1
-- title:
--   Theorem 2.4.9 — active, semiactive, pseudoactive and quasiactive schedules as minimal points
-- statement:
--   Consider a project with feasible region $\mathcal S=\mathcal S_T\cap\mathcal S_R$. A point $S$ of a set $\mathcal M\subseteq\mathbb R^{n+2}$ is a *minimal point* of $\mathcal M$ if there is no $S'\in\mathcal M$ with $S'\ne S$ and $S'\le S$. Let $S$ be a feasible schedule. Then:
--
--   1. (a) $S$ is active if and only if $S$ is a minimal point of $\mathcal S$;
--   2. (b) $S$ is semiactive if and only if $S$ is a minimal point of a (connected) component of $\mathcal S$;
--   3. (c) $S$ is pseudoactive if and only if $S$ is the minimal point of every order polyhedron $\mathcal S_T(O)$ belonging to a feasible strict order $O\subseteq O(S)$;
--   4. (d) $S$ is quasiactive if and only if $S$ is the minimal point of its schedule polyhedron $\mathcal S_T(O(S))$.
--
--   In words, $$\mathcal{AS},\ \mathcal{SAS},\ \mathcal{PAS},\ \mathcal{QAS}$$ are the minimal points of the feasible region, of its components, of the order polyhedra of feasible sub-orders, and of the schedule polyhedron, respectively.
--
--   The theorem translates the shift-based definitions of §2.4 into geometric properties of the feasible region; (d) gives a polynomial test for quasiactivity, and (c) is the basis of the local-minimality characterization of pseudoactive schedules.
--
--   **Formalization Note** The theorem is stated for feasible schedules $S$ (the classes of Definition 2.4.6 consist of feasible schedules; without this restriction (d) fails for time-feasible but resource-infeasible schedules). Minimal points use Mathlib's `Minimal` with the componentwise order on `Fin (n + 2) → ℝ`. Components are connected components (`connectedComponentIn`), while local shifts use continuous trajectories as in Definition 2.4.3.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, DOI 10.1007/978-3-540-24800-2, p. 43, Theorem 2.4.9 (proof pp. 43–44)

import Mathlib
import Definitions.Def_ProjSchedTW_ActiveSchedules_Project
import Definitions.Def_ProjSchedTW_ActiveSchedules_Shifts

namespace ProjSchedTW.ActiveSchedules

/-- Theorem 2.4.9 (p. 43). For a feasible schedule `S`:
(a) `S` is active iff it is a minimal point of the feasible region `𝒮`;
(b) `S` is semiactive iff it is a minimal point of a (connected) component of `𝒮`;
(c) `S` is pseudoactive iff it is the minimal point of every order polyhedron `S_T(O)` of a
feasible strict order `O ⊆ O(S)`;
(d) `S` is quasiactive iff it is the minimal point of its schedule polyhedron `S_T(O(S))`. -/
theorem minimal_point_characterization {n : ℕ} {K : Type} (P : Project n K)
    (S : Fin (n + 2) → ℝ) (hS : S ∈ feasibleSet P) :
    (IsActive P S ↔ Minimal (· ∈ feasibleSet P) S) ∧
      (IsSemiactive P S ↔
        ∃ x ∈ feasibleSet P, Minimal (· ∈ connectedComponentIn (feasibleSet P) x) S) ∧
      (IsPseudoactive P S ↔
        ∀ O : Set (Fin (n + 2) × Fin (n + 2)), IsFeasibleOrder P O → O ⊆ scheduleOrder P S →
          Minimal (· ∈ orderPolyhedron P O) S) ∧
      (IsQuasiactive P S ↔ Minimal (· ∈ orderPolyhedron P (scheduleOrder P S)) S) := by sorry

end ProjSchedTW.ActiveSchedules
