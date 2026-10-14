-- Prove2me | Theorems.Thm_Plasticity_U16_complete
-- name    : Plasticity.U16.complete
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T07:54:18.752591+00:00
-- url     : https://prove2.me/theorems/bad4f599-d8f7-4534-9a8b-77a1db8a8567
-- title:
--   Completion: a sphere-preserving map tangent to an onto isometry at $0$ equals it
-- statement:
--   Let $X$ be a real Banach space, $Y$ a real normed space, and $F\colon B_X\to B_Y$ nonexpansive with $F(S_X)\subseteq S_Y$.
--   Let $T\colon X\to Y$ be a surjective linear isometry and $C$ a real constant with
--   $$\|F(x)-Tx\|\le C\|x\|^2\qquad(x\in B_X).$$
--   Then $F=T$ on $B_X$.
--
--   Every functional norming $F(a)$, $a\in S_X$, also norms $Ta$, so $H=T^{-1}F$ is a nonexpansive self-map of $B_X$ with $\|a+H(a)\|=2$ on $S_X$, and common-face rigidity (A01) gives $H=I$.
-- source:
--   This repository: expositions/sphere_coverage_general.md §1, Steps 2 and 4; expositions/sphere_preservation_general.md §4, second paragraph

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.U16
theorem complete {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hmaps : Set.MapsTo F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hsphere : Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1))
    (T : X ≃ₗᵢ[ℝ] Y) (C : ℝ) (hT : ∀ x ∈ Metric.closedBall (0 : X) 1, ‖F x - T x‖ ≤ C * ‖x‖ ^ 2) :
    Set.EqOn F T (Metric.closedBall (0 : X) 1) := by sorry
end Plasticity.U16
