-- Prove2me | Theorems.Thm_Timetabling85_CourseColoring_figure4_feasible
-- name    : Timetabling85.CourseColoring.figure4_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:56:16.593774+00:00
-- url     : https://prove2.me/theorems/c0467f45-0b56-4a22-91aa-51067bfbbbf7
-- title:
--   §3.1, Figure 4, p. 157 — the printed schedule of the Figure 4 example is feasible in 4 periods
-- statement:
--   Consider the instance of Figure 4: courses $K_1, K_2, K_3$ with $1, 2, 2$ lectures; student 1 takes $K_1, K_2$; student 2 takes $K_2, K_3$. The schedule printed on the page,
--
--   $$\text{period }1: K_1, K_3;\quad \text{period }2: K_2;\quad \text{period }3: K_2;\quad \text{period }4: K_3,$$
--
--   is a feasible course schedule in $p = 4$ periods: no two lectures of one course share a period, and no student has two lectures at one period.
--
--   This checks the example the paper uses to illustrate the graph model of §3.1.
--
--   **Formalization Note** The instance and the schedule are the definitions `figure4` and `figure4Schedule`, with all indices starting at $0$.
-- source:
--   de Werra, An introduction to timetabling, Eur. J. Oper. Res. 19 (1985), p. 157, §3.1, Figure 4 and "The schedule corresponding to the coloring in Figure 4 is: …"

import Mathlib
import Definitions.Def_Timetabling85_CourseColoring_Figure4

namespace Timetabling85.CourseColoring

theorem figure4_feasible : figure4.IsFeasibleSchedule 4 figure4Schedule := by sorry

end Timetabling85.CourseColoring
