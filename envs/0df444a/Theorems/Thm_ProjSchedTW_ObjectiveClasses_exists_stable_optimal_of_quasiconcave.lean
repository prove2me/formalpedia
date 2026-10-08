-- Prove2me | Theorems.Thm_ProjSchedTW_ObjectiveClasses_exists_stable_optimal_of_quasiconcave
-- name    : ProjSchedTW.ObjectiveClasses.exists_stable_optimal_of_quasiconcave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:44:26.42128+00:00
-- url     : https://prove2.me/theorems/42813253-3890-4d45-bac1-06e2b26a6da1
-- title:
--   §3.3.6, p. 226 — a quasiconcave objective has a stable optimal schedule
-- statement:
--   Let $\mathcal S$ be the feasible region of problem $PS|temp,\bar d|f$ and let $f:\mathbb R^{n+2}_{\ge 0}\to\mathbb R$ be quasiconcave, that is,
--   $$f(\lambda S+(1-\lambda)S')\ \ge\ \min[f(S),f(S')]\qquad\text{for all } S,S'\in\mathbb R^{n+2}_{\ge 0},\ \lambda\in[0,1].$$
--   If $\mathcal S\ne\emptyset$, then there is a stable schedule (a feasible schedule admitting no pair of opposite global shifts) which is optimal, i.e. minimizes $f$ over $\mathcal S$.
--
--   This is the result for class 5 of the book's classification, which contains for example the weighted start-time objective $\sum v_iS_i$ and $-\sum\sum w_{ij}|S_j-S_i|$.
--
--   **Formalization Note** No continuity of $f$ is assumed, as on the page; the existence of a minimizer is part of the claim.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, DOI 10.1007/978-3-540-24800-2, §3.3.6, p. 226, class 5 of quasiconcave objective functions

import Mathlib
import Definitions.Def_ProjSchedTW_ObjectiveClasses_Project
import Definitions.Def_ProjSchedTW_ObjectiveClasses_Classes

namespace ProjSchedTW.ObjectiveClasses

/-- §3.3.6, p. 226 (class 5): for every quasiconcave objective function `f` there is a stable
schedule which is optimal for `PS|temp,d̄|f`, provided that `𝒮 ≠ ∅`. -/
theorem exists_stable_optimal_of_quasiconcave {n : ℕ} {K : Type} (P : Project n K)
    (f : (Fin (n + 2) → ℝ) → ℝ) (hf : IsQuasiconcave f) (hS : (feasibleSet P).Nonempty) :
    ∃ S : Fin (n + 2) → ℝ, IsStable P S ∧ IsOptimal P f S := by sorry

end ProjSchedTW.ObjectiveClasses
