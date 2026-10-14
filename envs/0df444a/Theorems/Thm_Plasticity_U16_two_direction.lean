-- Prove2me | Theorems.Thm_Plasticity_U16_two_direction
-- name    : Plasticity.U16.two_direction
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T07:54:18.326212+00:00
-- url     : https://prove2.me/theorems/a572a1fc-dd72-40da-aaae-b3443f800df3
-- title:
--   Two-direction estimate: $\|F(tv)+F(tw)+F(-t(v+w))\|\le 96t^2$
-- statement:
--   Let $X,Y$ be real normed spaces and $F\colon B_X\to B_Y$ nonexpansive with $F(S_X)\subseteq S_Y\subseteq F(B_X)$.
--   For all $v,w\in B_X$ and $0<t\le\tfrac12$,
--   $$\bigl\|F(tv)+F(tw)+F(-t(v+w))\bigr\|\le 96\,t^2 .$$
--
--   Dividing by $t$ and letting $t\downarrow0$ shows that the limit map $T=\lim_{t\downarrow0}F(t\,\cdot)/t$ is additive.
-- source:
--   This repository: expositions/sphere_preservation_general.md §3, estimate (12) and the line after it, valid under sphere coverage by expositions/sphere_coverage_general.md §1, Step 1

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.U16
theorem two_direction {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hmaps : Set.MapsTo F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hsphere : Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1))
    (hcover : Metric.sphere (0 : Y) 1 ⊆ F '' Metric.closedBall (0 : X) 1)
    (v w : X) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) :
    ‖F (t • v) + F (t • w) + F (-(t • (v + w)))‖ ≤ 96 * t ^ 2 := by sorry
end Plasticity.U16
