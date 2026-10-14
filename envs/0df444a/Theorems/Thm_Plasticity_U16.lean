-- Prove2me | Theorems.Thm_Plasticity_U16
-- name    : Plasticity.U16
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T07:40:29.181166+00:00
-- url     : https://prove2.me/theorems/7db30a91-7e0a-4b33-b52b-5e58b046b84f
-- title:
--   Sphere coverage suffices: a nonexpansive ball map restricting to a surjection of unit spheres is a linear isometry
-- statement:
--   Let $X$ and $Y$ be nonzero real Banach spaces and let $F\colon B_X\to B_Y$ be a nonexpansive map of their closed unit balls.
--   If $F(S_X)\subseteq S_Y$ and every unit vector of $Y$ is the image of some point of $B_X$, then $F$ is the restriction to $B_X$ of a surjective real-linear isometry $T\colon X\to Y$.
--   Coverage of interior targets, injectivity and inverse regularity are not assumed.
-- source:
--   This repository: claim U16 (claims/u.md); proof in expositions/sphere_coverage_general.md §1, with U10 §§1–3 and the Bishop–Phelps theorem

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity
theorem U16 {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [Nontrivial X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] [Nontrivial Y]
    (F : X → Y)
    (hmaps : Set.MapsTo F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hsphere : Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1))
    (hcover : Metric.sphere (0 : Y) 1 ⊆ F '' Metric.closedBall (0 : X) 1) :
    ∃ T : X ≃ₗᵢ[ℝ] Y, Set.EqOn F T (Metric.closedBall (0 : X) 1) := by sorry
end Plasticity
