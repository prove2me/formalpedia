-- Prove2me | Theorems.Thm_Timetabling85_TwoPeriod_timetable_iff_stable
-- name    : Timetabling85.TwoPeriod.timetable_iff_stable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:10.94244+00:00
-- url     : https://prove2.me/theorems/8fceee55-427f-496c-bf62-4b1c0e0a1e00
-- title:
--   Proof of Proposition 2.4, p. 155 — a timetable exists iff the conflict graph has n pairwise non-adjacent nodes
-- statement:
--   Let $I$ be an instance of the daily class–teacher problem CT4 with $m$ classes, $n$ teachers and $p$ periods, and let $G$ be its conflict graph: one node for each pair (teacher $t_j$, possible schedule of $t_j$), two nodes linked when they are different schedules of the same teacher or when they put the same class in the same period. Then
--   $$
--   \text{CT4 has a solution } \bar x \iff G \text{ contains a set of } n \text{ pairwise non-adjacent nodes.}
--   $$
--
--   This is the reduction on which de Werra's algorithm for Proposition 2.4 rests: in the two-period case it turns the timetabling question into the question of finding a stable set with one node from each pair $\{x_j,\bar x_j\}$.
--
--   **Formalization Note** The statement holds for every CT4 instance, without the two-period bound; the page's "graph $G$ with $2n$ nodes" is the case in which every teacher has exactly two schedules, while in general $G$ has $\sum_j \#\{\text{schedules of } t_j\}$ nodes. "Set of $n$ pairwise non-adjacent nodes" is Mathlib's `IsNIndepSet n`.
-- source:
--   de Werra, An introduction to timetabling, Eur. J. Oper. Res. 19 (1985), p. 155, Proof of Proposition 2.4 (construction of G and 'a timetable exists iff there is in G a set of n pairwise non adjacent nodes')

import Mathlib
import Definitions.Def_Timetabling85_TwoPeriod_CT4

namespace Timetabling85.TwoPeriod

theorem timetable_iff_stable {m n p : ℕ} (I : CT4Data m n p) :
    (∃ x : Fin m → Fin n → Fin p → Bool, IsSolution I x) ↔
      ∃ S : Finset (Node I), (conflictGraph I).IsNIndepSet n S := by sorry

end Timetabling85.TwoPeriod
