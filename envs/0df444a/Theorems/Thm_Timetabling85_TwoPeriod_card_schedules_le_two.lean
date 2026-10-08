-- Prove2me | Theorems.Thm_Timetabling85_TwoPeriod_card_schedules_le_two
-- name    : Timetabling85.TwoPeriod.card_schedules_le_two
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:00.180618+00:00
-- url     : https://prove2.me/theorems/4116f704-b36b-49b5-9bce-b937a78f9a0c
-- title:
--   Proof of Proposition 2.4, pp. 154–155 — a teacher available in at most 2 periods has at most 2 possible schedules
-- statement:
--   Consider an instance of the daily class–teacher problem CT4 with $m$ classes, $n$ teachers and $p$ periods, and fix a teacher $t_j$. Call a $0/1$ array $y=(y_{ik})$ a possible schedule of $t_j$ if $\sum_k y_{ik}=\bar r_{ij}$ for every class $c_i$, at most $\bar c_{jk}$ classes meet $t_j$ at each period $k$, and $c_i$ meets $t_j$ at period $k$ only if $\bar b_{ik}=1$. If teacher $t_j$ is available during at most $2$ periods, i.e. $\#\{k:\bar c_{jk}=1\}\le 2$, then
--   $$
--   \#\{\text{possible schedules of } t_j\}\le 2 .
--   $$
--
--   This is the step of the proof of Proposition 2.4 that gives every teacher at most two nodes $x_j,\bar x_j$ in the conflict graph.
--
--   **Formalization Note** The page says each teacher has *exactly* $2$ possible schedules, after the normalisation "one may clearly assume that all teachers are available for 2 periods exactly". Without that normalisation the number can be $0$, $1$ or $2$ (for example one lecture of a single class and two free periods gives two schedules, two lectures of the same class gives one), so the faithful content is the bound $\le 2$.
-- source:
--   de Werra, An introduction to timetabling, Eur. J. Oper. Res. 19 (1985), pp. 154–155, Proof of Proposition 2.4, first sentences

import Mathlib
import Definitions.Def_Timetabling85_TwoPeriod_CT4

namespace Timetabling85.TwoPeriod

theorem card_schedules_le_two {m n p : ℕ} (I : CT4Data m n p) (j : Fin n)
    (hj : (Finset.univ.filter fun k => I.cbar j k = true).card ≤ 2) :
    (schedules I j).card ≤ 2 := by sorry

end Timetabling85.TwoPeriod
