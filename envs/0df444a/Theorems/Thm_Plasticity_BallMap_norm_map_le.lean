-- Prove2me | Theorems.Thm_Plasticity_BallMap_norm_map_le
-- name    : Plasticity.BallMap.norm_map_le
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T19:03:18.771851+00:00
-- url     : https://prove2.me/theorems/206dd2dc-42c9-44b7-a3b4-45d6fe1ee640
-- title:
--   A nonexpansive map of a unit ball onto a unit ball does not increase norms
-- statement:
--   Let $X,Y$ be real normed spaces and let $F$ map the closed unit ball $B_X$ onto the closed unit ball $B_Y$ and be nonexpansive on $B_X$. Then $$\|F(x)\|\le\|x\|\qquad(x\in B_X).$$ It follows from $F(0)=0$ and nonexpansiveness.
-- source:
--   O. Zavarzina, Non-expansive bijections between unit balls of Banach spaces, Ann. Funct. Anal. 9 (2018), Theorem 2.3 (arXiv:1704.06961); for one ball B. Cascales, V. Kadets, J. Orihuela, E. J. Wingler, RACSAM 110 (2016), Theorem 2.3; this repository's claim U01 (claims/u.md)

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.BallMap
theorem norm_map_le {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (F : X → Y)
    (hsurj : Set.SurjOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (x : X) (hx : x ∈ Metric.closedBall (0 : X) 1) :
    ‖F x‖ ≤ ‖x‖ := by sorry
end Plasticity.BallMap
