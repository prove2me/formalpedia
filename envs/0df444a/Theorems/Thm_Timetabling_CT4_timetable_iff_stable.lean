-- Prove2me | Theorems.Thm_Timetabling_CT4_timetable_iff_stable
-- name    : Timetabling.CT4.timetable_iff_stable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:40:55.394034+00:00
-- url     : https://prove2.me/theorems/5b8481e3-b6aa-4d5a-a73d-1a102db3bc50
-- title:
--   A timetable exists iff the conflict graph has a stable set of $n$ nodes (corrected: every teacher needs a schedule)
-- statement:
--   Let $I$ be a well-formed CT4 instance with $n$ teachers, each available ($\bar c_{jk} = 1$) in at most two periods, and let $G$ be its conflict graph. Then
--
--   1. if every teacher has at least one possible schedule,
--   $$
--   \text{CT4 has a timetable} \iff G \text{ has a set of } n \text{ pairwise non-adjacent nodes;}
--   $$
--   2. if some teacher has no possible schedule, CT4 has no timetable.
--
--   This is the reduction of Proposition 2.4: timetabling becomes the search for a stable set of $n$ nodes in a graph with $2n$ nodes.
--
--   Differences from the source:
--   - correction: every teacher has exactly 2 possible schedules, so G always has 2n nodes with schedules → clause 1 assumes every teacher has at least one schedule; a teacher with one schedule has it on both nodes; reason: a teacher available in 1 period who must meet 2 classes has no schedule; its two nodes would carry the empty schedule and G could have a stable n-set while no timetable exists
--   - generalization: (no statement for a teacher without schedule) → clause 2: a teacher without a possible schedule makes CT4 infeasible; reason: covers the case excluded by the printed 'exactly 2'; the paper's case is clause 1
--   - reading: teacher available during at most 2 periods → hypothesis on c̄_jk; reason: availability enters CT4 only through c̄; weaker hypothesis
--   - encoding: nodes x_j, x̄_j → Fin n × Bool, (j, true) = x_j, 0-based; reason: labelling only; same graph
-- source:
--   de Werra (1985), proof of Proposition 2.4, p. 155, "We construct a graph G with 2n nodes ..." and "Then a timetable exists iff there is in G a set of n pairwise non adjacent nodes (i.e. a stable set [1])". D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib
import Definitions.Def_Timetabling_CT4_Instance_WellFormed
import Definitions.Def_Timetabling_CT4_Feasible
import Definitions.Def_Timetabling_CT4_conflictGraph

namespace Timetabling.CT4

/-- **A timetable exists iff the conflict graph has a stable set of `n` nodes.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), proof of Proposition 2.4, p. 155:
"We construct a graph G with 2n nodes [...] we link 2 nodes in G if the corresponding schedules
are not compatible (in particular, nodes x_j and x̄_j are linked)." and "Then a timetable exists
iff there is in G a set of n pairwise non adjacent nodes (i.e. a stable set [1])."

Let `I` be a well-formed CT4 instance with `n` teachers, each free (`c̄_jk = 1`) in at most 2
periods. Then

1. if every teacher has at least one possible schedule, CT4 has a timetable if and only if the
   conflict graph `conflictGraph I` has an independent set of `n` nodes;
2. if some teacher has no possible schedule, CT4 has no timetable. -/
theorem timetable_iff_stable {m n p : ℕ} (I : Instance m n p) (hI : I.WellFormed)
    (h2 : ∀ j, (Finset.univ.filter fun k => I.cbar j k = 1).card ≤ 2) :
    ((∀ j, teacherSchedules I j ≠ []) →
      ((∃ x, Feasible I x) ↔ ∃ s, (conflictGraph I).IsNIndepSet n s)) ∧
    ((∃ j, teacherSchedules I j = []) → ¬ ∃ x, Feasible I x) := by sorry

end Timetabling.CT4
