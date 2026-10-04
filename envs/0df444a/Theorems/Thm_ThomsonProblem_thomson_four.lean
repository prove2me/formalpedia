-- Prove2me | Theorems.Thm_ThomsonProblem_thomson_four
-- name    : ThomsonProblem.thomson_four
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T21:12:15.203434+00:00
-- url     : https://prove2.me/theorems/9b304ed3-8879-48d3-bb99-fc71b7e9267b
-- title:
--   Thomson problem, $N=4$: the regular tetrahedron is optimal
-- statement:
--   Let $x$ be the regular tetrahedron with vertices $\tfrac1{\sqrt3}(1,1,1)$, $\tfrac1{\sqrt3}(1,-1,-1)$, $\tfrac1{\sqrt3}(-1,1,-1)$, $\tfrac1{\sqrt3}(-1,-1,1)$. Then $x$ solves the Thomson problem for $N=4$ electrons: its points are 4 distinct points of the unit sphere, and for every configuration $y$ of 4 pairwise distinct points $y_0,\dots,y_{3}$ on the unit sphere,
--   $$
--   \sum_{0\le i<j\le 3}\frac{1}{\|x_i-x_j\|}\ \le\ \sum_{0\le i<j\le 3}\frac{1}{\|y_i-y_j\|} .
--   $$
--
--   The source lists $N=4$ among the mathematically exact solutions: the electrons reside at the vertices of a regular tetrahedron (energy $\approx 3.674234614$ in the source's table).
-- source:
--   Wikipedia, "Thomson problem" (as uploaded, PDF snapshot retrieved 2026-09-29/30), section "Known exact solutions", fourth bullet (N = 4).

import Definitions.Def_ThomsonProblem_defs

namespace ThomsonProblem

theorem thomson_four : IsEnergyMinimizer regularTetrahedron := by sorry

end ThomsonProblem
