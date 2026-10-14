-- Prove2me | Theorems.Thm_Plasticity_U16_norm_eq
-- name    : Plasticity.U16.norm_eq
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T07:54:19.960768+00:00
-- url     : https://prove2.me/theorems/f8680171-3811-4c24-be45-39831207f0d2
-- title:
--   Sphere coverage forces $F(0)=0$ and preservation of every norm
-- statement:
--   Let $X$ and $Y$ be real normed spaces with closed unit balls $B_X,B_Y$ and unit spheres $S_X,S_Y$, and let $F\colon B_X\to B_Y$ be nonexpansive.
--   Assume that $F(S_X)\subseteq S_Y$ and that every unit vector of $Y$ is the image of some point of $B_X$.
--   Then
--   $$F(0)=0\qquad\text{and}\qquad \|F(x)\|=\|x\|\quad(x\in B_X).$$
--
--   This is the first step of the sphere-coverage theorem (U16) and of the sphere-preservation theorem (U10): every later estimate compares images through their norms.
--
--   **Formalization Note** The map is a function on the whole space, constrained on the ball by `Set.MapsTo` and `LipschitzOnWith 1`; completeness and nontriviality are not needed.
-- source:
--   This repository: expositions/sphere_coverage_general.md §1, Step 1 (the U10 analogue is expositions/sphere_preservation_general.md §1, identity (1))

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.U16
theorem norm_eq {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hmaps : Set.MapsTo F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hsphere : Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1))
    (hcover : Metric.sphere (0 : Y) 1 ⊆ F '' Metric.closedBall (0 : X) 1) :
    F 0 = 0 ∧ ∀ x ∈ Metric.closedBall (0 : X) 1, ‖F x‖ = ‖x‖ := by sorry
end Plasticity.U16
