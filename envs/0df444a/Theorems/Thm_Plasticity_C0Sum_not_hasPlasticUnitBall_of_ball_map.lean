-- Prove2me | Theorems.Thm_Plasticity_C0Sum_not_hasPlasticUnitBall_of_ball_map
-- name    : Plasticity.C0Sum.not_hasPlasticUnitBall_of_ball_map
-- status  : Proved
-- author  : @scanstone
-- created : 2026-11-18T19:25:33.753061+00:00
-- url     : https://prove2.me/theorems/355ea7dc-ab78-4dff-82fd-7d5d24ee45db
-- title:
--   A non-isometric nonexpansive bijection $B_X\to B_Y$ makes the ball of $c_0(\mathbb N,X)\oplus_\infty c_0(\mathbb N,Y)$ nonplastic
-- statement:
--   Let $X,Y$ be real normed spaces and $F\colon B_X\to B_Y$ a nonexpansive bijection between their closed unit balls that is not an isometry.
--   Then the closed unit ball of $c_0(\mathbb N,X)\oplus_\infty c_0(\mathbb N,Y)$ is not plastic.
--   The witness is the bilateral shift over $\mathbb Z$ (copies of $X$ at indices $\le0$, copies of $Y$ at indices $\ge1$) that applies $F$ at the junction.
-- source:
--   K. A. Kurik, arXiv:2403.09245, Theorem 3.1 (stated there for ℓ∞-sums over ℤ; the c₀-sum variant is this repository's claim U21 and expositions/two_space_reduction.md)

import Definitions.Def_Plasticity_Basic
import Definitions.Def_Plasticity_C0Sum

namespace Plasticity
theorem C0Sum.not_hasPlasticUnitBall_of_ball_map {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : Metric.closedBall (0 : X) 1 → Metric.closedBall (0 : Y) 1)
    (hF : LipschitzWith 1 F) (hbij : Function.Bijective F) (hiso : ¬ Isometry F) :
    ¬ HasPlasticUnitBall (c0Sum (fun _ : ℕ => X) × c0Sum (fun _ : ℕ => Y)) := by sorry
end Plasticity
