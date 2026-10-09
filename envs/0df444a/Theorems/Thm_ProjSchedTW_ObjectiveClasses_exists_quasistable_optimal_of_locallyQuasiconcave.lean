-- Prove2me | Theorems.Thm_ProjSchedTW_ObjectiveClasses_exists_quasistable_optimal_of_locallyQuasiconcave
-- name    : ProjSchedTW.ObjectiveClasses.exists_quasistable_optimal_of_locallyQuasiconcave
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T10:44:57.394329+00:00
-- url     : https://prove2.me/theorems/5884ced4-108c-4799-834d-18ef71cdfd71
-- title:
--   Theorem 3.3.13 — a locally quasiconcave objective has a quasistable optimal schedule
-- statement:
--   Let $f:\mathbb R^{n+2}_{\ge 0}\to\mathbb R$ be locally quasiconcave: $f$ is lower semicontinuous on $\mathbb R^{n+2}_{\ge 0}$, and for each feasible schedule $S\in\mathcal S$, $f$ is quasiconcave on the equal-order set $\mathcal S_T^{=}(O(S))$, i.e.
--   $$f(\lambda S'+(1-\lambda)S'')\ \ge\ \min[f(S'),f(S'')]\qquad(S',S''\in\mathcal S_T^{=}(O(S)),\ \lambda\in[0,1]).$$
--   If $\mathcal S\ne\emptyset$, then there exists a quasistable schedule (a feasible schedule admitting no pair of opposite order-preserving shifts) which is optimal for $PS|temp,\bar d|f$, i.e. minimizes $f$ over the whole feasible region $\mathcal S$.
--
--   Class 7 contains the resource levelling objectives and the resource renting objective. Since there are only finitely many quasistable schedules, the theorem reduces the minimization of any such objective to a finite search, which is the basis of the enumeration schemes of Chapter 3.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, DOI 10.1007/978-3-540-24800-2, p. 235, Theorem 3.3.13

import Mathlib
import Definitions.Def_ProjSchedTW_ObjectiveClasses_Project
import Definitions.Def_ProjSchedTW_ObjectiveClasses_Classes

namespace ProjSchedTW.ObjectiveClasses

/-- Theorem 3.3.13 (p. 235): for a locally quasiconcave function `f`, there always exists a
quasistable schedule which is optimal for `PS|temp,d̄|f` provided that `𝒮 ≠ ∅`. -/
theorem exists_quasistable_optimal_of_locallyQuasiconcave {n : ℕ} {K : Type} (P : Project n K)
    (f : (Fin (n + 2) → ℝ) → ℝ) (hf : IsLocallyQuasiconcave P f)
    (hS : (feasibleSet P).Nonempty) :
    ∃ S : Fin (n + 2) → ℝ, IsQuasistable P S ∧ IsOptimal P f S := by sorry

end ProjSchedTW.ObjectiveClasses
