-- Prove2me | Theorems.Thm_Plasticity_U16_mixed_scale
-- name    : Plasticity.U16.mixed_scale
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T07:54:17.217268+00:00
-- url     : https://prove2.me/theorems/c0c0f3e9-9b23-4bfa-82ae-f03f5885fa35
-- title:
--   Mixed-scale estimate: $\|F(tv)/t+F(-uv)/u\|\le 8(t+u)$
-- statement:
--   Let $X,Y$ be real normed spaces and $F\colon B_X\to B_Y$ nonexpansive with $F(S_X)\subseteq S_Y\subseteq F(B_X)$.
--   For every unit vector $v\in S_X$ and all $0<t\le1$, $0<u\le1$,
--   $$\left\|\frac{F(tv)}{t}+\frac{F(-uv)}{u}\right\|\le 8(t+u).$$
--
--   With $u=t$ it shows that the difference quotients $F(tv)/t$ are Cauchy as $t\downarrow0$ and that their limits at $v$ and $-v$ are opposite; letting $u\downarrow0$ it bounds $\|F(x)-Tx\|$ by $8\|x\|^2$ for the limit map $T$.
-- source:
--   This repository: expositions/sphere_preservation_general.md §2, estimate (4), valid under sphere coverage by expositions/sphere_coverage_general.md §1, Step 1

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.U16
theorem mixed_scale {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hmaps : Set.MapsTo F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hsphere : Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1))
    (hcover : Metric.sphere (0 : Y) 1 ⊆ F '' Metric.closedBall (0 : X) 1)
    (v : X) (hv : ‖v‖ = 1) (t u : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) (hu0 : 0 < u) (hu1 : u ≤ 1) :
    ‖t⁻¹ • F (t • v) + u⁻¹ • F (-(u • v))‖ ≤ 8 * (t + u) := by sorry
end Plasticity.U16
