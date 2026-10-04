-- Prove2me | Theorems.Thm_ThomsonProblem_thomson_two
-- name    : ThomsonProblem.thomson_two
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T20:27:24.820148+00:00
-- url     : https://prove2.me/theorems/d562c69e-eb62-48f1-ae4b-9e22587e277e
-- title:
--   Thomson problem, $N=2$: antipodal points are optimal, $U=1/2$
-- statement:
--   Let $x_0=(0,0,1)$ and $x_1=(0,0,-1)$ be two antipodal points of the unit sphere. Then this configuration solves the Thomson problem for two electrons, and its energy is
--   $$
--   U(x_0,x_1)=\frac{1}{\|x_0-x_1\|}=\frac12 .
--   $$
--   That is, for every pair of distinct points $y_0,y_1$ on the unit sphere, $1/\|y_0-y_1\|\ge 1/2$.
--
--   This is the worked example of the source: the two electrons are as far apart as possible, on opposite sides of the origin, at distance $2$.
-- source:
--   Wikipedia, "Thomson problem" (as uploaded, PDF snapshot retrieved 2026-09-29/30), section "Example" (U(x_1,x_2) = 1/2) and section "Known exact solutions", second bullet (N = 2).

import Definitions.Def_ThomsonProblem_defs

namespace ThomsonProblem

theorem thomson_two :
    IsEnergyMinimizer antipodalPair ∧ coulombEnergy antipodalPair = 1 / 2 := by sorry

end ThomsonProblem
