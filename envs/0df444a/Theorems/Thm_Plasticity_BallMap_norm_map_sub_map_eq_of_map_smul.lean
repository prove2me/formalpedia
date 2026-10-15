-- Prove2me | Theorems.Thm_Plasticity_BallMap_norm_map_sub_map_eq_of_map_smul
-- name    : Plasticity.BallMap.norm_map_sub_map_eq_of_map_smul
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-15T02:24:11.801277+00:00
-- url     : https://prove2.me/theorems/ae029f53-1a2d-48dd-a8b9-196b75e2cdaf
-- title:
--   A nonexpansive ball map that keeps the sphere is isometric between points on whose rays it is homogeneous
-- statement:
--   Let $X,Y$ be real normed spaces and $F\colon X\to Y$ a map with $\|F(x)-F(x')\|\le\|x-x'\|$ on the closed unit ball $B_X$ and $F(S_X)\subseteq S_Y$. If $x,y\in X$ satisfy $F(tx)=tF(x)$ and $F(ty)=tF(y)$ for all $t\in[-1,1]$, then $\|F(x)-F(y)\|=\|x-y\|$ (points outside $B_X$ are rescaled into it).
--   For a unit vector $u$ and $0<a\le1$, writing $2F(u)=(F(u)+aF(y))+(F(u)-aF(x))+a(F(x)-F(y))$ gives $2\le\|u+ay\|+\|u-ax\|+a\|F(x)-F(y)\|$; differentiating at $a=0$ at a point $u$ of the plane of $x,y$ where $s\mapsto\|x-y+sy\|$ is differentiable (Rademacher's theorem) and letting $u\to(x-y)/\|x-y\|$ gives $\|x-y\|\le\|F(x)-F(y)\|$.
-- source:
--   O. Zavarzina, Non-expansive bijections between unit balls of Banach spaces, Ann. Funct. Anal. 9 (2018), Lemmas 2.4–2.5 (arXiv:1704.06961), from B. Cascales, V. Kadets, J. Orihuela, E. J. Wingler, RACSAM 110 (2016), Lemmas 2.4–2.5; stated here without bijectivity or completeness, which the proof does not use

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.BallMap
theorem norm_map_sub_map_eq_of_map_smul {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hsphere : Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1))
    (x y : X)
    (hFx : ∀ t ∈ Set.Icc (-1 : ℝ) 1, F (t • x) = t • F x)
    (hFy : ∀ t ∈ Set.Icc (-1 : ℝ) 1, F (t • y) = t • F y) :
    ‖F x - F y‖ = ‖x - y‖ := by sorry
end Plasticity.BallMap
