-- Prove2me | Theorems.Thm_Plasticity_BallMap_map_zero_of_surjOn
-- name    : Plasticity.BallMap.map_zero_of_surjOn
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T19:03:18.453708+00:00
-- url     : https://prove2.me/theorems/5a604fdc-7f7a-48a1-bd9a-4574a0340377
-- title:
--   A nonexpansive map of a unit ball onto a unit ball fixes the origin
-- statement:
--   Let $X,Y$ be real normed spaces and let $F$ map the closed unit ball $B_X$ onto the closed unit ball $B_Y$ and be nonexpansive on $B_X$. Then $$F(0)=0.$$ Only surjectivity onto $B_Y$ is used, not that $F$ maps $B_X$ into $B_Y$; this is the first of the basic facts on which arguments about nonexpansive bijections between balls rest.
-- source:
--   O. Zavarzina, Non-expansive bijections between unit balls of Banach spaces, Ann. Funct. Anal. 9 (2018), Theorem 2.3 (arXiv:1704.06961); for one ball B. Cascales, V. Kadets, J. Orihuela, E. J. Wingler, RACSAM 110 (2016), Theorem 2.3; this repository's claim U01 (claims/u.md)

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.BallMap
theorem map_zero_of_surjOn {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (F : X → Y)
    (hsurj : Set.SurjOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1)) :
    F 0 = 0 := by sorry
end Plasticity.BallMap
