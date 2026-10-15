-- Prove2me | Theorems.Thm_Plasticity_BallMap_norm_map_eq_of_mapsTo_sphere
-- name    : Plasticity.BallMap.norm_map_eq_of_mapsTo_sphere
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T19:03:20.922993+00:00
-- url     : https://prove2.me/theorems/37dc3520-9c7a-45d3-adbc-c1a8221904a0
-- title:
--   A nonexpansive surjection of unit balls that maps the sphere into the sphere preserves norms
-- statement:
--   Let $X,Y$ be real normed spaces and let $F$ map the closed unit ball $B_X$ onto the closed unit ball $B_Y$ and be nonexpansive on $B_X$. If $F$ maps the unit sphere of $X$ into the unit sphere of $Y$, then $$\|F(x)\|=\|x\|\qquad(x\in B_X).$$
-- source:
--   O. Zavarzina, Non-expansive bijections between unit balls of Banach spaces, Ann. Funct. Anal. 9 (2018), Theorem 2.3 (arXiv:1704.06961); for one ball B. Cascales, V. Kadets, J. Orihuela, E. J. Wingler, RACSAM 110 (2016), Theorem 2.3; this repository's claim U01 (claims/u.md)

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.BallMap
theorem norm_map_eq_of_mapsTo_sphere {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (F : X → Y)
    (hsurj : Set.SurjOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hsphere : Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1))
    (x : X) (hx : x ∈ Metric.closedBall (0 : X) 1) :
    ‖F x‖ = ‖x‖ := by sorry
end Plasticity.BallMap
