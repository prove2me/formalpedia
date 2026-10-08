-- Prove2me | Theorems.Thm_ProjSchedTW_ObjectiveClasses_exists_active_optimal_of_regular
-- name    : ProjSchedTW.ObjectiveClasses.exists_active_optimal_of_regular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:44:22.280986+00:00
-- url     : https://prove2.me/theorems/0a57cc46-de25-4016-961b-de5c7211d9ce
-- title:
--   §3.3.2, p. 221 — a regular objective has an active optimal schedule
-- statement:
--   Let $\mathcal S$ be the feasible region of problem $PS|temp,\bar d|f$ and let $f:\mathbb R^{n+2}_{\ge 0}\to\mathbb R$ be regular, that is, $S\le S'$ implies $f(S)\le f(S')$ for all $S,S'\in\mathbb R^{n+2}_{\ge 0}$. If $\mathcal S\ne\emptyset$, then there is an active schedule $S$ (a feasible schedule admitting no global left-shift) which is optimal:
--   $$S\in\mathcal S\ \text{active},\qquad f(S)\le f(S')\ \text{ for all } S'\in\mathcal S.$$
--
--   This is the result for class 1 of the book's classification: regular objectives such as the project duration, the maximum lateness or weighted flow time can be minimized over the active schedules alone.
--
--   **Formalization Note** No continuity of $f$ is assumed, as on the page; the existence of a minimizer is part of the claim.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, DOI 10.1007/978-3-540-24800-2, §3.3.2, p. 221, class 1 of regular objective functions

import Mathlib
import Definitions.Def_ProjSchedTW_ObjectiveClasses_Project
import Definitions.Def_ProjSchedTW_ObjectiveClasses_Classes

namespace ProjSchedTW.ObjectiveClasses

/-- §3.3.2, p. 221 (class 1): for every regular objective function `f` there is an active
schedule which is optimal for `PS|temp,d̄|f`, provided that `𝒮 ≠ ∅`. -/
theorem exists_active_optimal_of_regular {n : ℕ} {K : Type} (P : Project n K)
    (f : (Fin (n + 2) → ℝ) → ℝ) (hf : IsRegular f) (hS : (feasibleSet P).Nonempty) :
    ∃ S : Fin (n + 2) → ℝ, IsActive P S ∧ IsOptimal P f S := by sorry

end ProjSchedTW.ObjectiveClasses
