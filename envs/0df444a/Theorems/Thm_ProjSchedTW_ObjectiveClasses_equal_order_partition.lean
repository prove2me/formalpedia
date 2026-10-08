-- Prove2me | Theorems.Thm_ProjSchedTW_ObjectiveClasses_equal_order_partition
-- name    : ProjSchedTW.ObjectiveClasses.equal_order_partition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T10:44:37.126984+00:00
-- url     : https://prove2.me/theorems/861df57b-0d4c-4a64-857f-ae4eec939d2e
-- title:
--   §3.3.7, Eq. (3.3.11) — the equal-order sets form a finite partition of the feasible region
-- statement:
--   Let $\mathcal S$ be the feasible region of a project with prescribed maximum duration $\bar d$, and for $S\in\mathcal S$ let $\mathcal S_T^{=}(O(S))$ be the equal-order set of $S$, the set of time-feasible schedules inducing the same strict order $O(S)$. Then
--   $$\mathcal S=\bigcup_{S\in\mathcal S}\mathcal S_T^{=}(O(S)),$$
--   there are only finitely many distinct equal-order sets $\mathcal S_T^{=}(O(S))$, $S\in\mathcal S$, and two distinct ones are disjoint.
--
--   The equal-order sets thus form a finite partition of the feasible region. This is the frame in which classes 6 and 7 of objective functions are defined: a locally regular or locally quasiconcave function is only required to behave well on each piece of this partition.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, DOI 10.1007/978-3-540-24800-2, §3.3.7, p. 229, Eq. (3.3.11) and the sentence following it

import Mathlib
import Definitions.Def_ProjSchedTW_ObjectiveClasses_Project
import Definitions.Def_ProjSchedTW_ObjectiveClasses_Classes

namespace ProjSchedTW.ObjectiveClasses

/-- §3.3.7, p. 229, Eq. (3.3.11): the feasible region is the union of the equal-order sets
`S_T^=(O(S))`, `S ∈ 𝒮`; there are only finitely many distinct equal-order sets, and distinct ones
are disjoint (a finite partition of `𝒮`). -/
theorem equal_order_partition {n : ℕ} {K : Type} (P : Project n K) :
    (feasibleSet P = ⋃ S ∈ feasibleSet P, equalOrderSet P S) ∧
      (equalOrderSet P '' feasibleSet P).Finite ∧
      ∀ S ∈ feasibleSet P, ∀ S' ∈ feasibleSet P,
        equalOrderSet P S ≠ equalOrderSet P S' →
          Disjoint (equalOrderSet P S) (equalOrderSet P S') := by sorry

end ProjSchedTW.ObjectiveClasses
