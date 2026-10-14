-- Prove2me | Theorems.Thm_Plasticity_U16_onto
-- name    : Plasticity.U16.onto
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T07:54:17.418718+00:00
-- url     : https://prove2.me/theorems/1a36187c-7cbd-4c9a-ac9b-ba952cc2e34f
-- title:
--   Sphere coverage makes the linearization onto (via Bishop–Phelps)
-- statement:
--   Let $X,Y$ be real Banach spaces and $F\colon B_X\to B_Y$ nonexpansive with $F(S_X)\subseteq S_Y\subseteq F(B_X)$.
--   Let $T\colon X\to Y$ be a linear isometric embedding and $C$ a real constant with
--   $$\|F(x)-Tx\|\le C\|x\|^2\qquad(x\in B_X).$$
--   Then $T$ is surjective.
--
--   This replaces the use of surjectivity of $F$ in the sphere-preservation theorem; the argument combines alignment of $Ta$ with every functional norming $F(a)$ and the density of norm-attaining functionals.
-- source:
--   This repository: expositions/sphere_coverage_general.md §1, Steps 2–3

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.U16
theorem onto {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (F : X → Y)
    (hmaps : Set.MapsTo F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hsphere : Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1))
    (hcover : Metric.sphere (0 : Y) 1 ⊆ F '' Metric.closedBall (0 : X) 1)
    (T : X →ₗᵢ[ℝ] Y) (C : ℝ) (hT : ∀ x ∈ Metric.closedBall (0 : X) 1, ‖F x - T x‖ ≤ C * ‖x‖ ^ 2) :
    Function.Surjective T := by sorry
end Plasticity.U16
