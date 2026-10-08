-- Prove2me | Theorems.Thm_ProjSchedTW_ActiveSchedules_quasiactive_integral
-- name    : ProjSchedTW.ActiveSchedules.quasiactive_integral
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T16:05:56.795985+00:00
-- url     : https://prove2.me/theorems/f75c0c70-b686-48e3-8a02-32784aff496d
-- title:
--   Remark 2.4.10 (b) — quasiactive schedules are integer-valued
-- statement:
--   Let the arc weights $\delta_{ij}$ be integers and the durations $p_i$ nonnegative integers.
--
--   1. Every quasiactive schedule $S$ has $S_0=0$, and for each activity $j\ne 0$ there is an activity $i$ such that $$S_j=S_i+\delta_{ij}\ \text{ with }\langle i,j\rangle\in E\qquad\text{or}\qquad S_j=S_i+p_i\ \text{ with } i\neq j.$$
--   2. Consequently every quasiactive schedule is integer-valued: $\mathcal{QAS}\subseteq\mathbb Z^{n+2}_{\ge 0}$.
--   3. The feasible region is nonempty if and only if there is an integer-valued optimal schedule: $\mathcal S\neq\emptyset \iff \mathcal{OS}\cap\mathbb Z^{n+2}_{\ge 0}\neq\emptyset$.
--
--   The integrality justifies restricting all enumeration schemes for $PS|temp|C_{\max}$ to integer start times.
--
--   **Formalization Note** Integrality of $\delta$ and $p$ is built into the project data (`ℤ` and `ℕ`). The condition $i\neq j$ in the second alternative excludes the trivial identity $S_{n+1}=S_{n+1}+p_{n+1}$; the book's $i$ is an activity with $(i,j)\in O(S)$.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, DOI 10.1007/978-3-540-24800-2, p. 44, Remark 2.4.10 (b)

import Mathlib
import Definitions.Def_ProjSchedTW_ActiveSchedules_Project
import Definitions.Def_ProjSchedTW_ActiveSchedules_Shifts

namespace ProjSchedTW.ActiveSchedules

/-- Remark 2.4.10 (b) (p. 44): a quasiactive schedule has `S_0 = 0` and every other start time
equals `S_i + δ_ij` for an arc `⟨i, j⟩` or `S_i + p_i` for an activity `i ≠ j`; hence
quasiactive schedules are integer-valued, and `𝒮 ≠ ∅` iff there is an integer-valued optimal
schedule. -/
theorem quasiactive_integral {n : ℕ} {K : Type} (P : Project n K) :
    (∀ S : Fin (n + 2) → ℝ, IsQuasiactive P S →
      S 0 = 0 ∧ ∀ j : Fin (n + 2), j ≠ 0 → ∃ i : Fin (n + 2),
        ((i, j) ∈ P.E ∧ S j = S i + (P.δ i j : ℝ)) ∨ (i ≠ j ∧ S j = S i + (P.p i : ℝ))) ∧
    (∀ S : Fin (n + 2) → ℝ, IsQuasiactive P S → ∀ i : Fin (n + 2), ∃ m : ℕ, S i = (m : ℝ)) ∧
    ((feasibleSet P).Nonempty ↔
      ∃ S : Fin (n + 2) → ℝ, IsOptimal P S ∧ ∀ i : Fin (n + 2), ∃ m : ℕ, S i = (m : ℝ)) := by sorry

end ProjSchedTW.ActiveSchedules
