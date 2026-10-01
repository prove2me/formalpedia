-- Prove2me | Theorems.Thm_ThomsonProblem_thomson_six
-- name    : ThomsonProblem.thomson_six
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T21:33:44.199981+00:00
-- url     : https://prove2.me/theorems/6078810e-c200-47e7-9653-555ba1572299
-- title:
--   Thomson problem, $N=6$: the regular octahedron is optimal
-- statement:
--   Let $x$ be the regular octahedron $\pm e_1,\pm e_2,\pm e_3$. Then $x$ solves the Thomson problem for $N=6$ electrons: its points are 6 distinct points of the unit sphere, and for every configuration $y$ of 6 pairwise distinct points $y_0,\dots,y_{5}$ on the unit sphere,
--   $$
--   \sum_{0\le i<j\le 5}\frac{1}{\|x_i-x_j\|}\ \le\ \sum_{0\le i<j\le 5}\frac{1}{\|y_i-y_j\|} .
--   $$
--
--   The source states that for $N=6$ the electrons reside at the vertices of a regular octahedron (V. A. Yudin, 1992/1993); energy $\approx 9.985281374$ in the source's table.
-- source:
--   Wikipedia, "Thomson problem" (as uploaded, PDF snapshot retrieved 2026-09-29/30), section "Known exact solutions", sixth bullet (N = 6, Yudin 1992).

import Definitions.Def_ThomsonProblem_defs

namespace ThomsonProblem

theorem thomson_six : IsEnergyMinimizer regularOctahedron := by sorry

end ThomsonProblem
