-- Prove2me | Theorems.Thm_Timetabling_CT4_teacherSchedules_spec
-- name    : Timetabling.CT4.teacherSchedules_spec
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:40:22.484707+00:00
-- url     : https://prove2.me/theorems/61dde884-f81a-4a28-8e61-aa2c9cf6c849
-- title:
--   At most two possible schedules per teacher (corrected: exactly 2 → at most 2)
-- statement:
--   Let $I$ be a well-formed CT4 instance and $t_j$ a teacher with $\bar c_{jk} = 1$ for at most two periods $k$. Then
--
--   1. an array $y = (y_{ik})$ is a possible schedule of $t_j$ if and only if it is the 0/1 indicator of the slot set of one of the entries $s$ of $\mathsf{teacherSchedules}(I, j)$:
--   $$
--   y_{ik} = \begin{cases} 1 & (i,k) \in s,\\ 0 & \text{otherwise;}\end{cases}
--   $$
--   2. $\mathsf{teacherSchedules}(I, j)$ has at most two entries.
--
--   This is the first step of the proof of Proposition 2.4: it reduces each teacher to a choice between at most two nodes $x_j$, $\bar x_j$ of the conflict graph.
--
--   Differences from the source:
--   - correction: each teacher has exactly 2 possible schedules → at most 2 entries in teacherSchedules I j; reason: false as printed: a teacher available at periods 1, 2 who must meet one class twice has the single schedule {(c_i,1),(c_i,2)}; a teacher with no lecture has only the empty schedule
--   - generalization: all teachers available for exactly 2 periods (after 'one may clearly assume') → at most 2 periods with c̄_jk = 1; reason: covers the teachers the proof reduces away; specializes to the paper's case of exactly 2
--   - reading: teacher available during at most 2 periods → hypothesis on c̄_jk (available and not preassigned); reason: availability enters CT4 only through c̄; the c̄ hypothesis is weaker than raw availability
--   - encoding: possible schedule of a teacher → LocallyFeasible slice y and lists of slots (i, k), 0-based indices; reason: the constraints (12)-(15) restricted to one teacher; same instances
-- source:
--   de Werra (1985), proof of Proposition 2.4, pp. 154-155, "One may clearly assume that all teachers are available for 2 periods exactly ... so each teacher has exactly 2 possible schedules". D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib
import Definitions.Def_Timetabling_CT4_Instance_WellFormed
import Definitions.Def_Timetabling_CT4_LocallyFeasible
import Definitions.Def_Timetabling_CT4_teacherSchedules

namespace Timetabling.CT4

/-- **At most two possible schedules per teacher** (corrected: "exactly 2" → "at most 2").
de Werra, *An introduction to timetabling*, EJOR 19 (1985), proof of Proposition 2.4,
pp. 154–155, "One may clearly assume that all teachers are available for 2 periods exactly
(since a teacher who is available for 1 period has a fixed schedule); so each teacher has
exactly 2 possible schedules."

Let `I` be a well-formed CT4 instance and `t_j` a teacher with `c̄_jk = 1` for at most 2 periods
`k`. Then

1. a slice `y` is a possible schedule of `t_j` (`LocallyFeasible`) if and only if it is the 0/1
   indicator of the slot set of some entry of `teacherSchedules I j`;
2. `teacherSchedules I j` has at most 2 entries.

**Formalization Note.** Correction of the printed "exactly 2": a teacher free at two periods who
must meet one class twice has a single possible schedule. -/
theorem teacherSchedules_spec {m n p : ℕ} (I : Instance m n p) (hI : I.WellFormed) (j : Fin n)
    (hj : (Finset.univ.filter fun k => I.cbar j k = 1).card ≤ 2) :
    (∀ y : Fin m → Fin p → ℕ, LocallyFeasible I j y ↔
      ∃ s ∈ teacherSchedules I j, ∀ i k, y i k = if (i, k) ∈ s then 1 else 0) ∧
    (teacherSchedules I j).length ≤ 2 := by sorry

end Timetabling.CT4
