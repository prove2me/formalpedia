-- Prove2me | Theorems.Thm_ProjSchedTW_ObjectiveClasses_exists_quasiactive_optimal_of_locallyRegular
-- name    : ProjSchedTW.ObjectiveClasses.exists_quasiactive_optimal_of_locallyRegular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:44:48.377602+00:00
-- url     : https://prove2.me/theorems/b167a7e0-80e2-4ddd-bc07-bf8f83c52d78
-- title:
--   Theorem 3.3.9 — a locally regular objective has a quasiactive optimal schedule
-- statement:
--   Let $f:\mathbb R^{n+2}_{\ge 0}\to\mathbb R$ be locally regular: $f$ is lower semicontinuous on $\mathbb R^{n+2}_{\ge 0}$, and for each feasible schedule $S\in\mathcal S$, $f$ is regular on the equal-order set $\mathcal S_T^{=}(O(S))$, i.e. $S'\le S''$ implies $f(S')\le f(S'')$ for $S',S''\in\mathcal S_T^{=}(O(S))$. If $\mathcal S\ne\emptyset$, then there exists a quasiactive schedule (a feasible schedule admitting no order-preserving left-shift) which is optimal for $PS|temp,\bar d|f$:
--   $$\exists\,S\in\mathcal S\ \text{quasiactive with}\ f(S)\le f(S')\ \text{ for all } S'\in\mathcal S.$$
--
--   Class 6 contains the resource investment objective and the changeover-time objective. The theorem says that for these objectives the search can be restricted to the finite set of quasiactive schedules.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, DOI 10.1007/978-3-540-24800-2, p. 231, Theorem 3.3.9

import Mathlib
import Definitions.Def_ProjSchedTW_ObjectiveClasses_Project
import Definitions.Def_ProjSchedTW_ObjectiveClasses_Classes

namespace ProjSchedTW.ObjectiveClasses

/-- Theorem 3.3.9 (p. 231): for a locally regular function `f`, there always exists a
quasiactive schedule which is optimal for `PS|temp,d̄|f` provided that `𝒮 ≠ ∅`. -/
theorem exists_quasiactive_optimal_of_locallyRegular {n : ℕ} {K : Type} (P : Project n K)
    (f : (Fin (n + 2) → ℝ) → ℝ) (hf : IsLocallyRegular P f) (hS : (feasibleSet P).Nonempty) :
    ∃ S : Fin (n + 2) → ℝ, IsQuasiactive P S ∧ IsOptimal P f S := by sorry

end ProjSchedTW.ObjectiveClasses
