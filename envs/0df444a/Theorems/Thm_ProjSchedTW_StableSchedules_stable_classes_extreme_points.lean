-- Prove2me | Theorems.Thm_ProjSchedTW_StableSchedules_stable_classes_extreme_points
-- name    : ProjSchedTW.StableSchedules.stable_classes_extreme_points
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T01:15:23.046268+00:00
-- url     : https://prove2.me/theorems/f9ba7999-6f08-468d-9557-c18e6af9a132
-- title:
--   Theorem 3.2.10 — antiactive, stable, semistable, pseudostable and quasistable schedules as maximal and extreme points
-- statement:
--   Let $\mathcal S$ be the feasible region of a project with time windows, scarce renewable resources and deadline $\bar d$, and let $S\in\mathcal S$ be a feasible schedule. Then:
--
--   1. (a) $S$ is antiactive if and only if $S$ is a maximal point of $\mathcal S$;
--   2. (b) $S$ is stable if and only if $S$ is an extreme point of $\mathcal S$;
--   3. (c) $S$ is semistable if and only if $S$ is an extreme point of a component of $\mathcal S$;
--   4. (d) $S$ is pseudostable if and only if $S$ is an extreme point of every order polytope $\mathcal S_T(O)$ belonging to a feasible strict order $O\subseteq O(S)$;
--   5. (e) $S$ is quasistable if and only if $S$ is an extreme point of the schedule polytope $\mathcal S_T(O(S))$.
--
--   The five classes are defined through shifts: no global right-shift, and no pair of opposite global, local, order-monotone or order-preserving shifts. In symbols,
--   $$\overline{\mathcal{AS}}=\max\mathcal S,\qquad \mathcal{SS}=\operatorname{ext}\mathcal S,\qquad \mathcal{QSS}=\{S\in\mathcal S\mid S\in\operatorname{ext}\mathcal S_T(O(S))\}.$$
--
--   This is the counterpart for nonregular objectives of Theorem 2.4.9, which describes active schedules as minimal points. The finiteness results and the spanning-tree description of §3.2, and the classification of objective functions in §3.3, rest on it.
--
--   **Formalization Note** The component in (c) is the connected component of $\mathcal S$ containing $S$ (Mathlib `connectedComponentIn`). Local shifts use continuous trajectories in $\mathcal S$. Connected and path components of $\mathcal S$ coincide because $\mathcal S$ is a finite union of polytopes (Theorem 2.3.7), but that is part of what has to be proved. Extreme points are Mathlib's `Set.extremePoints ℝ`. The feasibility of $S$ is a hypothesis: the book states the theorem for schedules of its classes, which are feasible by definition.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 211, Theorem 3.2.10 (a)–(e)

import Mathlib
import Definitions.Def_ProjSchedTW_StableSchedules_Project
import Definitions.Def_ProjSchedTW_StableSchedules_Shifts

namespace ProjSchedTW.StableSchedules

/-- Theorem 3.2.10 (p. 211). For a feasible schedule `S`:
(a) `S` is antiactive iff `S` is a maximal point of `𝒮`;
(b) `S` is stable iff `S` is an extreme point of `𝒮`;
(c) `S` is semistable iff `S` is an extreme point of a component of `𝒮` (necessarily the one
containing `S`);
(d) `S` is pseudostable iff `S` is an extreme point of every order polytope `S_T(O)` belonging
to a feasible strict order `O ⊆ O(S)`;
(e) `S` is quasistable iff `S` is an extreme point of the schedule polytope `S_T(O(S))`. -/
theorem stable_classes_extreme_points {n : ℕ} {K : Type} (P : Project n K)
    (S : Fin (n + 2) → ℝ) (hS : S ∈ feasibleSet P) :
    (IsAntiactive P S ↔ Maximal (· ∈ feasibleSet P) S) ∧
    (IsStable P S ↔ S ∈ (feasibleSet P).extremePoints ℝ) ∧
    (IsSemistable P S ↔ S ∈ (connectedComponentIn (feasibleSet P) S).extremePoints ℝ) ∧
    (IsPseudostable P S ↔
      ∀ O : Set (Fin (n + 2) × Fin (n + 2)), IsFeasibleOrder P O → O ⊆ scheduleOrder P S →
        S ∈ (orderPolytope P O).extremePoints ℝ) ∧
    (IsQuasistable P S ↔ S ∈ (orderPolytope P (scheduleOrder P S)).extremePoints ℝ) := by sorry

end ProjSchedTW.StableSchedules
