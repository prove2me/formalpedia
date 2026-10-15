-- Prove2me | Theorems.Thm_Plasticity_BallMap_map_smul_of_map_mem_extremePoints
-- name    : Plasticity.BallMap.map_smul_of_map_mem_extremePoints
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T19:03:19.997006+00:00
-- url     : https://prove2.me/theorems/01168763-828e-4b37-9157-a5cfb943dc71
-- title:
--   A nonexpansive bijection of unit balls is linear on the diameter through the preimage of an extreme point
-- statement:
--   Let $X,Y$ be real normed spaces and $F\colon B_X\to B_Y$ a nonexpansive bijection of their closed unit balls. If $x\in B_X$ and $F(x)$ is an extreme point of $B_Y$, then $$F(tx)=tF(x)\qquad(-1\le t\le1).$$
-- source:
--   O. Zavarzina, Non-expansive bijections between unit balls of Banach spaces, Ann. Funct. Anal. 9 (2018), Theorem 2.3 (arXiv:1704.06961); for one ball B. Cascales, V. Kadets, J. Orihuela, E. J. Wingler, RACSAM 110 (2016), Theorem 2.3; this repository's claim U01 (claims/u.md)

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.BallMap
theorem map_smul_of_map_mem_extremePoints {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (F : X → Y)
    (hbij : Set.BijOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (x : X) (hx : x ∈ Metric.closedBall (0 : X) 1)
    (hext : F x ∈ (Metric.closedBall (0 : Y) 1).extremePoints ℝ)
    (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    F (t • x) = t • F x := by sorry
end Plasticity.BallMap
