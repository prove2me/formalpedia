-- Prove2me | Theorems.Thm_Plasticity_U10
-- name    : Plasticity.U10
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T07:40:22.686856+00:00
-- url     : https://prove2.me/theorems/deb778c6-e299-40c3-9676-f074ec633d55
-- title:
--   Sphere preservation suffices: a sphere-preserving nonexpansive surjection of unit balls is a linear isometry
-- statement:
--   Let $X$ and $Y$ be nonzero real Banach spaces and let $F\colon B_X\to B_Y$ be a nonexpansive map of the closed unit ball of $X$ onto the closed unit ball of $Y$.
--   If $F$ maps the unit sphere $S_X$ into the unit sphere $S_Y$, then $F$ is the restriction to $B_X$ of a surjective real-linear isometry $T\colon X\to Y$.
--   No injectivity, inverse regularity, smoothness, reflexivity or extreme-point hypothesis is assumed.
-- source:
--   This repository: claim U10 (claims/u.md); proof in expositions/sphere_preservation_general.md §§1–4

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity
theorem U10 {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [Nontrivial X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] [Nontrivial Y]
    (F : X → Y)
    (hmaps : Set.MapsTo F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hsurj : Set.SurjOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hsphere : Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1)) :
    ∃ T : X ≃ₗᵢ[ℝ] Y, Set.EqOn F T (Metric.closedBall (0 : X) 1) := by sorry
end Plasticity
