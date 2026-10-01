-- Prove2me | Theorems.Thm_ThomsonProblem_thomson_five
-- name    : ThomsonProblem.thomson_five
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T21:27:34.724018+00:00
-- url     : https://prove2.me/theorems/a9100c80-d47f-48b4-bea3-cfb4071b893c
-- title:
--   Thomson problem, $N=5$: the triangular bipyramid is optimal
-- statement:
--   Let $x$ be the triangular bipyramid: the poles $(0,0,\pm1)$ together with the equilateral triangle $(1,0,0)$, $(-\tfrac12,\pm\tfrac{\sqrt3}2,0)$ on the equator. Then $x$ solves the Thomson problem for $N=5$ electrons: its points are 5 distinct points of the unit sphere, and for every configuration $y$ of 5 pairwise distinct points $y_0,\dots,y_{4}$ on the unit sphere,
--   $$
--   \sum_{0\le i<j\le 4}\frac{1}{\|x_i-x_j\|}\ \le\ \sum_{0\le i<j\le 4}\frac{1}{\|y_i-y_j\|} .
--   $$
--
--   The source states that for $N=5$ the electrons reside at the vertices of a triangular bipyramid (R. Schwartz, *The five-electron case of Thomson's problem*, Experimental Mathematics 22 (2013), arXiv:1001.3702); energy $\approx 6.474691495$ in the source's table.
-- source:
--   Wikipedia, "Thomson problem" (as uploaded, PDF snapshot retrieved 2026-09-29/30), section "Known exact solutions", fifth bullet (N = 5, Schwartz 2013).

import Definitions.Def_ThomsonProblem_defs

namespace ThomsonProblem

theorem thomson_five : IsEnergyMinimizer triangularBipyramid := by sorry

end ThomsonProblem
