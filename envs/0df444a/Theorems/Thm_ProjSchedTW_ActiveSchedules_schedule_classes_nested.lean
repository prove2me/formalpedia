-- Prove2me | Theorems.Thm_ProjSchedTW_ActiveSchedules_schedule_classes_nested
-- name    : ProjSchedTW.ActiveSchedules.schedule_classes_nested
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T16:05:26.260917+00:00
-- url     : https://prove2.me/theorems/6bfde4e3-3df1-4293-ac92-ac6195e82155
-- title:
--   §2.4, p. 42, Fig. 2.4.5 — active ⊆ semiactive ⊆ pseudoactive ⊆ quasiactive
-- statement:
--   For every schedule $S$ of a project:
--
--   1. if $S$ is active, it is semiactive;
--   2. if $S$ is semiactive, it is pseudoactive;
--   3. if $S$ is pseudoactive, it is quasiactive.
--
--   In set notation,
--   $$\mathcal{AS}\subseteq\mathcal{SAS}\subseteq\mathcal{PAS}\subseteq\mathcal{QAS}\subseteq\mathcal S .$$
--
--   The chain orders the four candidate sets that enumeration methods for $PS|temp|C_{\max}$ search.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, DOI 10.1007/978-3-540-24800-2, §2.4, p. 42, text before Figure 2.4.5

import Mathlib
import Definitions.Def_ProjSchedTW_ActiveSchedules_Project
import Definitions.Def_ProjSchedTW_ActiveSchedules_Shifts

namespace ProjSchedTW.ActiveSchedules

/-- §2.4, p. 42 and Figure 2.4.5: active schedules are semiactive, semiactive schedules are
pseudoactive, and pseudoactive schedules are quasiactive (`AS ⊆ SAS ⊆ PAS ⊆ QAS`). -/
theorem schedule_classes_nested {n : ℕ} {K : Type} (P : Project n K)
    (S : Fin (n + 2) → ℝ) :
    (IsActive P S → IsSemiactive P S) ∧
      (IsSemiactive P S → IsPseudoactive P S) ∧
      (IsPseudoactive P S → IsQuasiactive P S) := by sorry

end ProjSchedTW.ActiveSchedules
