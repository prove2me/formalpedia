-- Prove2me | Theorems.Thm_ThomsonProblem_thomson_three
-- name    : ThomsonProblem.thomson_three
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T20:53:34.114948+00:00
-- url     : https://prove2.me/theorems/d6a4fd35-be23-47f0-a9b4-28c5e2ca7d6c
-- title:
--   Thomson problem, $N=3$: the equilateral triangle on a great circle is optimal
-- statement:
--   Let $x$ be the equilateral triangle $(1,0,0)$, $(-\tfrac12,\tfrac{\sqrt3}2,0)$, $(-\tfrac12,-\tfrac{\sqrt3}2,0)$ inscribed in the equator. Then $x$ solves the Thomson problem for $N=3$ electrons: its points are 3 distinct points of the unit sphere, and for every configuration $y$ of 3 pairwise distinct points $y_0,\dots,y_{2}$ on the unit sphere,
--   $$
--   \sum_{0\le i<j\le 2}\frac{1}{\|x_i-x_j\|}\ \le\ \sum_{0\le i<j\le 2}\frac{1}{\|y_i-y_j\|} .
--   $$
--
--   The source states that for $N=3$ the electrons reside at the vertices of an equilateral triangle about any great circle (Föppl 1912). Since the energy is invariant under rotations of the sphere, it suffices to treat the equator.
-- source:
--   Wikipedia, "Thomson problem" (as uploaded, PDF snapshot retrieved 2026-09-29/30), section "Known exact solutions", third bullet (N = 3, Föppl 1912).

import Definitions.Def_ThomsonProblem_defs

namespace ThomsonProblem

theorem thomson_three : IsEnergyMinimizer equilateralTriangle := by sorry

end ThomsonProblem
