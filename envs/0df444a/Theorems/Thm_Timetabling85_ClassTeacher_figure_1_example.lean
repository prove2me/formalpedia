-- Prove2me | Theorems.Thm_Timetabling85_ClassTeacher_figure_1_example
-- name    : Timetabling85.ClassTeacher.figure_1_example
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:18.400046+00:00
-- url     : https://prove2.me/theorems/f2679d3c-a75e-4176-a747-8d25ccaf2162
-- title:
--   Figure 1 example, pp. 153–154 — the printed weekly timetable solves CT3 for p = 3 days
-- statement:
--   Take two classes $c_1,c_2$, three teachers $t_1,t_2,t_3$, $p=3$ days and the requirement matrix
--   $$R=\begin{pmatrix}1&2&4\\3&0&2\end{pmatrix}.$$
--   The paper's solution, day by day,
--   $$x_{\cdot\cdot1}=\begin{pmatrix}0&0&2\\1&0&0\end{pmatrix},\quad x_{\cdot\cdot2}=\begin{pmatrix}0&1&1\\1&0&1\end{pmatrix},\quad x_{\cdot\cdot3}=\begin{pmatrix}1&1&1\\1&0&1\end{pmatrix},$$
--   is a solution of CT3: it schedules every lecture exactly once and satisfies the balance constraints (8), (9) and (10).
--
--   This is the worked example illustrating Proposition 2.3.
--
--   **Formalization Note** The page labels the three matrices "$x_{ij1}$, $x_{ij2}$ and $x_{ij2}$"; the third label is a misprint for $x_{ij3}$, and the third matrix is used for day 3. The blank entry $(c_2,t_2)$ of $R$ is $0$.
-- source:
--   de Werra, An introduction to timetabling, Eur. J. Oper. Res. 19 (1985), pp. 153–154, §2.1, example of Figure 1

import Mathlib
import Definitions.Def_Timetabling85_ClassTeacher_Problems

namespace Timetabling85.ClassTeacher

/-- The requirement matrix of Figure 1 (de Werra 1985, pp. 153–154): two classes, three teachers. -/
theorem figure_1_example :
    IsCT3 (m := 2) (n := 3) ![![1, 2, 4], ![3, 0, 2]] 3
      (fun i j k => (![![![0, 0, 2], ![1, 0, 0]],
                       ![![0, 1, 1], ![1, 0, 1]],
                       ![![1, 1, 1], ![1, 0, 1]]] : Fin 3 → Fin 2 → Fin 3 → ℕ) k i j) := by sorry

end Timetabling85.ClassTeacher
