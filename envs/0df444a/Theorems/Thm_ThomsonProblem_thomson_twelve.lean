-- Prove2me | Theorems.Thm_ThomsonProblem_thomson_twelve
-- name    : ThomsonProblem.thomson_twelve
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T21:44:10.973824+00:00
-- url     : https://prove2.me/theorems/80a025b9-9bcf-4c55-850a-2a07494642da
-- title:
--   Thomson problem, $N=12$: the regular icosahedron is optimal
-- statement:
--   Let $x$ be the regular icosahedron whose vertices are $(0,\pm1,\pm\varphi)$, $(\pm1,\pm\varphi,0)$, $(\pm\varphi,0,\pm1)$ divided by $\sqrt{1+\varphi^2}$, with $\varphi=\tfrac{1+\sqrt5}2$. Then $x$ solves the Thomson problem for $N=12$ electrons: its points are 12 distinct points of the unit sphere, and for every configuration $y$ of 12 pairwise distinct points $y_0,\dots,y_{11}$ on the unit sphere,
--   $$
--   \sum_{0\le i<j\le 11}\frac{1}{\|x_i-x_j\|}\ \le\ \sum_{0\le i<j\le 11}\frac{1}{\|y_i-y_j\|} .
--   $$
--
--   The source states that for $N=12$ the electrons reside at the vertices of a regular icosahedron (N. N. Andreev, *An extremal property of the icosahedron*, East J. Approx. 2 (1996)); energy $\approx 49.165253058$ in the source's table.
-- source:
--   Wikipedia, "Thomson problem" (as uploaded, PDF snapshot retrieved 2026-09-29/30), section "Known exact solutions", seventh bullet (N = 12, Andreev 1996).

import Definitions.Def_ThomsonProblem_defs

namespace ThomsonProblem

theorem thomson_twelve : IsEnergyMinimizer regularIcosahedron := by sorry

end ThomsonProblem
