-- Prove2me | Theorems.Thm_Plasticity_BallMap_mem_sphere_of_map_mem_sphere
-- name    : Plasticity.BallMap.mem_sphere_of_map_mem_sphere
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T19:03:19.374696+00:00
-- url     : https://prove2.me/theorems/967173f1-755e-4b99-9803-b06af2a28286
-- title:
--   Preimages of unit vectors under a nonexpansive surjection of unit balls are unit vectors
-- statement:
--   Let $X,Y$ be real normed spaces and $F\colon B_X\to B_Y$ a nonexpansive map of the closed unit balls onto $B_Y$. If $x\in B_X$ and $\|F(x)\|=1$, then $$\|x\|=1.$$ The proof compares $x$ with a preimage of $-F(x)$.
-- source:
--   O. Zavarzina, Non-expansive bijections between unit balls of Banach spaces, Ann. Funct. Anal. 9 (2018), Theorem 2.3 (arXiv:1704.06961); for one ball B. Cascales, V. Kadets, J. Orihuela, E. J. Wingler, RACSAM 110 (2016), Theorem 2.3; this repository's claim U01 (claims/u.md)

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.BallMap
theorem mem_sphere_of_map_mem_sphere {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (F : X → Y)
    (hsurj : Set.SurjOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (x : X) (hx : x ∈ Metric.closedBall (0 : X) 1) (hs : F x ∈ Metric.sphere (0 : Y) 1) :
    x ∈ Metric.sphere (0 : X) 1 := by sorry
end Plasticity.BallMap
