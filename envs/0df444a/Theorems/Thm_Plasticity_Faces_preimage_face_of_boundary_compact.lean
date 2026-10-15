-- Prove2me | Theorems.Thm_Plasticity_Faces_preimage_face_of_boundary_compact
-- name    : Plasticity.Faces.preimage_face_of_boundary_compact
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-15T00:33:59.836112+00:00
-- url     : https://prove2.me/theorems/00277a1c-47d2-4725-af01-a47444ebd668
-- title:
--   If the boundary preimage of a face is compact, extreme and symmetric, the preimage is a face of the same dimension
-- statement:
--   Under the hypotheses of the card `Plasticity.Faces.reflected_preimage_eq_cone`, except that $C$ may have any finite dimension, including $0$, $D=B_X\cap F^{-1}(C)$ is a compact sphere face of $B_X$ of the same finite dimension as $C$, $B_X\cap F^{-1}(-C)=-D$, and $B_X\cap F^{-1}(\partial C)=\partial D$.
-- source:
--   This repository: expositions/faces/codirected_compactness.md (claim F11), Lemma 2, Steps 5–6

import Definitions.Def_Plasticity_Faces
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.Faces
open scoped Pointwise
theorem preimage_face_of_boundary_compact {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hbij : Set.BijOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (C : Set Y) (hC : IsSphereFace C) (hfin : FiniteDimensional ℝ (vectorSpan ℝ C))
    (hAc : IsCompact (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' intrinsicFrontier ℝ C))
    (hAe : IsExtreme ℝ (Metric.closedBall (0 : X) 1)
      (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' intrinsicFrontier ℝ C))
    (hAs : ∀ x ∈ Metric.closedBall (0 : X) 1,
      F x ∈ intrinsicFrontier ℝ C ↔ -F (-x) ∈ intrinsicFrontier ℝ C) :
    IsSphereFace (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' C) ∧
    IsCompact (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' C) ∧
    FiniteDimensional ℝ (vectorSpan ℝ (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' C)) ∧
    Module.finrank ℝ (vectorSpan ℝ (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' C)) =
      Module.finrank ℝ (vectorSpan ℝ C) ∧
    Metric.closedBall (0 : X) 1 ∩ F ⁻¹' (-C) = -(Metric.closedBall (0 : X) 1 ∩ F ⁻¹' C) ∧
    Metric.closedBall (0 : X) 1 ∩ F ⁻¹' (intrinsicFrontier ℝ C) =
      intrinsicFrontier ℝ (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' C) := by sorry
end Plasticity.Faces
