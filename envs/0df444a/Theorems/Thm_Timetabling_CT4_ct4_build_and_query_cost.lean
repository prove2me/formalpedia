-- Prove2me | Theorems.Thm_Timetabling_CT4_ct4_build_and_query_cost
-- name    : Timetabling.CT4.ct4_build_and_query_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:44:13.47567+00:00
-- url     : https://prove2.me/theorems/ecbd8df3-8a9b-478d-9aa4-fb1c868427af
-- title:
--   The conflict graph is built and queried in constant time per teacher
-- statement:
--   There are absolute constants $C_1$ and $q_0$ such that for every well-formed CT4 instance $I$ in which every teacher is available ($\bar c_{jk} = 1$) in at most two periods:
--
--   1. for every teacher $t_j$, the procedure $\mathsf{readSchedules}(I, j)$ returns the possible schedules $\mathsf{teacherSchedules}(I, j)$ of $t_j$ after at most $C_1$ ticks;
--   2. for all nodes $u$, $w$, the test $\mathsf{compat}(I, u, w)$ returns whether $u$ and $w$ are linked in the conflict graph $G$ after at most $q_0$ ticks.
--
--   The constants depend on nothing: not on $m$, $n$, $p$ or $I$. Hence the $2n$ nodes of $G$ are available in $O(n)$ time and each adjacency query costs $O(1)$, which is what lets the $O(n^2)$ bound of the Remark carry over to CT4.
--
--   Differences from the source:
--   - reading: teacher available during at most 2 periods → hypothesis on c̄_jk; reason: availability enters CT4 only through c̄; weaker hypothesis
--   - reading: the instance of CT4 (as in Table 1) → the input includes the per-teacher lists of available periods and classes, read through ticked accessors; reason: without them the cost of finding a teacher's free periods grows with p, and the O(n^2) of Proposition 2.4 is false
--   - encoding: constructing G and testing compatibility of schedules (cost implicit in 'O(n^2)') → tick bounds C₁ per teacher and q₀ per query, with correctness of the returned values; reason: unit-cost RAM model; the page states the construction, the cost is the step of its O(n^2) count
-- source:
--   de Werra (1985), proof of Proposition 2.4, p. 155, "We construct a graph G with 2n nodes (where n is the number of teachers) as follows: ...". D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib
import Definitions.Def_Timetabling_CT4_Instance_WellFormed
import Definitions.Def_Timetabling_CT4_conflictGraph
import Definitions.Def_Timetabling_CT4_readSchedules
import Definitions.Def_Timetabling_CT4_compat

namespace Timetabling.CT4

/-- **The conflict graph is built and queried in constant time per teacher.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), proof of Proposition 2.4, p. 155:
"We construct a graph G with 2n nodes (where n is the number of teachers) as follows: For teacher
t_j introduce 2 nodes x_j, x̄_j corresponding to his possible schedules; we link 2 nodes in G if
the corresponding schedules are not compatible (in particular, nodes x_j and x̄_j are linked)."

There are absolute constants `C₁`, `q₀` such that for every well-formed CT4 instance `I` in which
every teacher is free (`c̄_jk = 1`) in at most 2 periods:

1. for every teacher `t_j` and tick count `s`, `readSchedules I j` returns
   `teacherSchedules I j` after at most `C₁` ticks;
2. for all nodes `u`, `w` and tick count `s`, `compat I u w` returns the adjacency of `u` and
   `w` in `conflictGraph I` after at most `q₀` ticks.

The constants do not depend on `m`, `n`, `p` or `I`. -/
theorem ct4_build_and_query_cost :
    ∃ C₁ q₀ : ℕ, ∀ {m n p : ℕ} (I : Instance m n p), I.WellFormed →
      (∀ j, (Finset.univ.filter fun k => I.cbar j k = 1).card ≤ 2) →
      (∀ j s, ∃ t ≤ C₁, (readSchedules I j).run s = (teacherSchedules I j, s + t)) ∧
      (∀ u w s, ∃ t ≤ q₀, (compat I u w).run s = (decide ((conflictGraph I).Adj u w), s + t)) := by sorry

end Timetabling.CT4
