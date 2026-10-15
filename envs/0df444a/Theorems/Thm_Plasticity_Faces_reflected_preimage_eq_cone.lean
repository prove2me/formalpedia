-- Prove2me | Theorems.Thm_Plasticity_Faces_reflected_preimage_eq_cone
-- name    : Plasticity.Faces.reflected_preimage_eq_cone
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-15T00:33:58.079835+00:00
-- url     : https://prove2.me/theorems/5839736e-7f4b-47a1-8e54-c9fccece6542
-- title:
--   The reflected preimage of a face is the cone over the boundary preimage from any interior preimage
-- statement:
--   Let $F\colon B_X\to B_Y$ be a nonexpansive bijection of the unit balls of real normed spaces, $C$ a sphere face of $B_Y$ of finite dimension $n\ge1$, and suppose that $A=B_X\cap F^{-1}(\partial C)$ is compact, an extreme subset of $B_X$, and symmetric in the sense that $F(x)\in\partial C$ iff $-F(-x)\in\partial C$. Then $D'=\{x\in B_X:-F(-x)\in C\}$ is compact and, for every $u\in B_X$ with $F(u)$ in the relative interior of $C$, $D'$ is the union of the segments $[u,a]$, $a\in A$.
-- source:
--   This repository: expositions/faces/codirected_compactness.md (claim F11), Lemma 2, Steps 1–4

import Definitions.Def_Plasticity_Faces
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.Faces
theorem reflected_preimage_eq_cone {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hbij : Set.BijOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (C : Set Y) (hC : IsSphereFace C) (hn : 1 ≤ Module.finrank ℝ (vectorSpan ℝ C))
    (hAc : IsCompact (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' intrinsicFrontier ℝ C))
    (hAe : IsExtreme ℝ (Metric.closedBall (0 : X) 1)
      (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' intrinsicFrontier ℝ C))
    (hAs : ∀ x ∈ Metric.closedBall (0 : X) 1,
      F x ∈ intrinsicFrontier ℝ C ↔ -F (-x) ∈ intrinsicFrontier ℝ C) :
    IsCompact {x | x ∈ Metric.closedBall (0 : X) 1 ∧ -F (-x) ∈ C} ∧
    ∀ u ∈ Metric.closedBall (0 : X) 1, F u ∈ C → F u ∉ intrinsicFrontier ℝ C →
      ∀ x, (x ∈ Metric.closedBall (0 : X) 1 ∧ -F (-x) ∈ C) ↔
        ∃ a ∈ Metric.closedBall (0 : X) 1 ∩ F ⁻¹' intrinsicFrontier ℝ C,
          x ∈ segment ℝ u a := by sorry
end Plasticity.Faces
