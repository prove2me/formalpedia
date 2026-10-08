-- Prove2me | Theorems.Thm_ProjSchedTW_StableSchedules_quasistable_tight_neighbor
-- name    : ProjSchedTW.StableSchedules.quasistable_tight_neighbor
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T01:15:48.891584+00:00
-- url     : https://prove2.me/theorems/b5068197-ae37-4128-ba0b-136d9f3b3abb
-- title:
--   Remark 3.2.7 — every activity of a quasistable schedule is tied to another; quasistable schedules are integer-valued
-- statement:
--   Let $S$ be a quasistable schedule. Then for each activity $i\in V$:
--
--   1. either there is an activity $j\ne i$ with $S_i+p_i=S_j$, or with $\langle i,j\rangle\in E$ and $S_i+\delta_{ij}=S_j$;
--   2. or there is an activity $h\ne i$ with $S_i=S_h+p_h$, or with $\langle h,i\rangle\in E$ and $S_i=S_h+\delta_{hi}$.
--
--   Consequently $S$ is integer-valued:
--   $$S\in\mathbb Z^{n+2}.$$
--   This holds because all durations and time lags are integers and $S_0=0$.
--
--   Integrality means that searches over quasistable schedules, and over all their subclasses, can be restricted to integer start times.
--
--   **Formalization Note** The book's $\delta_{ij}$ is the weight of an arc of $N$, so the time-lag alternatives require $\langle i,j\rangle\in E$ (resp. $\langle h,i\rangle\in E$). The activity $j$ (resp. $h$) is required to differ from $i$; otherwise the statement would hold trivially for the fictitious activities $0$ and $n+1$, which have duration $0$.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 210, Remark 3.2.7

import Mathlib
import Definitions.Def_ProjSchedTW_StableSchedules_Project
import Definitions.Def_ProjSchedTW_StableSchedules_Shifts

namespace ProjSchedTW.StableSchedules

/-- Remark 3.2.7 (p. 210). Let `S` be quasistable. Then every activity `i` is tied to another
activity: there is `j ≠ i` with `S_i + p_i = S_j` or (`⟨i,j⟩ ∈ E` and `S_i + δ_ij = S_j`), or
there is `h ≠ i` with `S_i = S_h + p_h` or (`⟨h,i⟩ ∈ E` and `S_i = S_h + δ_hi`). Consequently every
quasistable schedule is integer-valued. -/
theorem quasistable_tight_neighbor {n : ℕ} {K : Type} (P : Project n K)
    (S : Fin (n + 2) → ℝ) (hS : IsQuasistable P S) :
    (∀ i : Fin (n + 2),
      (∃ j, j ≠ i ∧ (S i + (P.p i : ℝ) = S j ∨ ((i, j) ∈ P.E ∧ S i + (P.δ i j : ℝ) = S j))) ∨
      (∃ h, h ≠ i ∧ (S i = S h + (P.p h : ℝ) ∨ ((h, i) ∈ P.E ∧ S i = S h + (P.δ h i : ℝ))))) ∧
    ∀ i : Fin (n + 2), ∃ z : ℤ, S i = z := by sorry

end ProjSchedTW.StableSchedules
