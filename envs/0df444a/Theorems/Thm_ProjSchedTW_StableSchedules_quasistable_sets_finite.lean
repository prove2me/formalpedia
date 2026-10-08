-- Prove2me | Theorems.Thm_ProjSchedTW_StableSchedules_quasistable_sets_finite
-- name    : ProjSchedTW.StableSchedules.quasistable_sets_finite
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T01:15:33.088652+00:00
-- url     : https://prove2.me/theorems/142c75df-c03d-443c-8098-c06773656349
-- title:
--   Proposition 3.2.13 — the set of quasistable schedules and its subsets in Fig. 3.2.6 are finite
-- statement:
--   For every project, the following sets of schedules are finite: the set $\mathcal{QSS}$ of quasistable schedules and all of its subsets shown in Fig. 3.2.6,
--   $$\mathcal{QSS},\ \mathcal{PSS},\ \mathcal{SSS},\ \mathcal{SS},\ \overline{\mathcal{AS}},\ \mathcal{QAS},\ \mathcal{PAS},\ \mathcal{SAS},\ \mathcal{AS}.$$
--   These are the pseudostable, semistable, stable, antiactive, quasiactive, pseudoactive, semiactive and active schedules.
--
--   For every class of objective functions of §3.3, the book finds an optimal schedule in one of these sets. The proposition shows that each such search runs over a finite candidate set.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 215, Proposition 3.2.13 and Fig. 3.2.6

import Mathlib
import Definitions.Def_ProjSchedTW_StableSchedules_Project
import Definitions.Def_ProjSchedTW_StableSchedules_Shifts

namespace ProjSchedTW.StableSchedules

/-- Proposition 3.2.13 (p. 215). The set `QSS` of quasistable schedules and all of its subsets
shown in Fig. 3.2.6 (`PSS`, `SSS`, `SS`, `\overline{AS}`, `QAS`, `PAS`, `SAS`, `AS`) are finite. -/
theorem quasistable_sets_finite {n : ℕ} {K : Type} (P : Project n K) :
    {S | IsQuasistable P S}.Finite ∧ {S | IsPseudostable P S}.Finite ∧
    {S | IsSemistable P S}.Finite ∧ {S | IsStable P S}.Finite ∧
    {S | IsAntiactive P S}.Finite ∧ {S | IsQuasiactive P S}.Finite ∧
    {S | IsPseudoactive P S}.Finite ∧ {S | IsSemiactive P S}.Finite ∧
    {S | IsActive P S}.Finite := by sorry

end ProjSchedTW.StableSchedules
