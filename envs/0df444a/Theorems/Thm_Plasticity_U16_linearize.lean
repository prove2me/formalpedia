-- Prove2me | Theorems.Thm_Plasticity_U16_linearize
-- name    : Plasticity.U16.linearize
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T07:54:19.521986+00:00
-- url     : https://prove2.me/theorems/08ab8825-1048-430c-ba37-bba3f2b56f5b
-- title:
--   Linearization: a linear isometric embedding $T$ with $\|F(x)-Tx\|\le 8\|x\|^2$
-- statement:
--   Let $X$ be a real normed space, $Y$ a real Banach space, and $F\colon B_X\to B_Y$ nonexpansive with $F(S_X)\subseteq S_Y\subseteq F(B_X)$.
--   Then there is a real-linear isometric embedding $T\colon X\to Y$ (that is, $T$ is linear and $\|Tx\|=\|x\|$ for all $x$) such that
--   $$\|F(x)-Tx\|\le 8\|x\|^2\qquad(x\in B_X).$$
--
--   In particular $F$ is Fréchet differentiable at $0$ with derivative $T$, and $Tv=\lim_{t\downarrow0}F(tv)/t$. Surjectivity of $T$ is not part of the statement.
--
--   **Formalization Note** $T$ is a Mathlib linear isometry `X →ₗᵢ[ℝ] Y`, which need not be onto.
-- source:
--   This repository: expositions/sphere_preservation_general.md §§2–3, estimates (7)–(9) and the conclusion of §3; under sphere coverage, expositions/sphere_coverage_general.md §1, Step 1, display (1)

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.U16
theorem linearize {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (F : X → Y)
    (hmaps : Set.MapsTo F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hsphere : Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1))
    (hcover : Metric.sphere (0 : Y) 1 ⊆ F '' Metric.closedBall (0 : X) 1) :
    ∃ T : X →ₗᵢ[ℝ] Y, ∀ x ∈ Metric.closedBall (0 : X) 1, ‖F x - T x‖ ≤ 8 * ‖x‖ ^ 2 := by sorry
end Plasticity.U16
