-- Prove2me | Theorems.Thm_Plasticity_U16_basic_estimate
-- name    : Plasticity.U16.basic_estimate
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T07:54:17.075935+00:00
-- url     : https://prove2.me/theorems/329d7aa9-bb0c-4b0b-89ce-ecdc78c6c436
-- title:
--   The anchor estimate: an actual preimage opposite a defect bounds the defect by scalar norms
-- statement:
--   Let $X,Y$ be real normed spaces and $F\colon B_X\to B_Y$ nonexpansive with $F(S_X)\subseteq S_Y\subseteq F(B_X)$.
--   Let $x_i\in B_X$ and $c_i\ge0$ for $i$ in a finite index set, and suppose
--   $$D=\sum_i c_i\,F(x_i)\neq0 .$$
--   Let $a\in B_X$ satisfy $F(a)=-D/\|D\|$.
--   Then for every $b\in B_X$ with $\|b-a\|\le\tfrac14$,
--   $$\frac{\|D\|}{2}\;\le\;\sum_i c_i\,\|b-x_i\|\;-\;\Bigl(\sum_i c_i\Bigr)\|b\| .$$
--
--   The right side involves only norms in $X$, so it can be averaged over a family of anchors $b$; this is how the defect $D$ of a linear relation among images is bounded in the sphere-preservation theorem.
-- source:
--   This repository: expositions/sphere_preservation_general.md §1, estimate (3), used verbatim under sphere coverage by expositions/sphere_coverage_general.md §1, Step 1

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.U16
theorem basic_estimate {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hmaps : Set.MapsTo F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hsphere : Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1))
    (hcover : Metric.sphere (0 : Y) 1 ⊆ F '' Metric.closedBall (0 : X) 1)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (x : ι → X)
    (hc : ∀ i ∈ s, 0 ≤ c i) (hx : ∀ i ∈ s, x i ∈ Metric.closedBall (0 : X) 1)
    (hD : ∑ i ∈ s, c i • F (x i) ≠ 0)
    (a : X) (ha : a ∈ Metric.closedBall (0 : X) 1)
    (hFa : F a = -(‖∑ i ∈ s, c i • F (x i)‖⁻¹ • ∑ i ∈ s, c i • F (x i)))
    (b : X) (hb : b ∈ Metric.closedBall (0 : X) 1) (hba : ‖b - a‖ ≤ 1 / 4) :
    ‖∑ i ∈ s, c i • F (x i)‖ / 2 ≤ ∑ i ∈ s, c i * ‖b - x i‖ - (∑ i ∈ s, c i) * ‖b‖ := by sorry
end Plasticity.U16
