-- Prove2me | Theorems.Thm_Plasticity_Faces_exists_isCompact_boundary_preimage_subset
-- name    : Plasticity.Faces.exists_isCompact_boundary_preimage_subset
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-15T00:33:57.815398+00:00
-- url     : https://prove2.me/theorems/377d4805-c829-4efc-b21a-d3a3e7ee674b
-- title:
--   If the smaller faces behave, the preimage of the relative boundary of a face is relatively compact
-- statement:
--   Let $X,Y$, $F$ and $C$ be as in the card `Plasticity.Faces.matchesFace_of_finiteDimensional`, with $\dim C=n$, and suppose that every face $C'\subseteq C$ of $B_Y$ contained in the sphere with $\dim C'<n$ satisfies the conclusions of the face theorem (`MatchesFace F C'`). Then the preimage $B_X\cap F^{-1}(\partial C)$ of the relative boundary of $C$ lies in a compact set.
--   The proof traps it in the smallest face of the preimage $q$ of a relative-interior point: for each boundary preimage $a$, the path $(\lambda+v)q-va$ crosses $\lambda\partial C$, which is exactly covered by $\lambda B_X\cap F^{-1}(\partial C)$, so $q$ lies strictly between $a$ and another boundary preimage.
-- source:
--   This repository: expositions/faces/finite_faces_boundary_crossing.md, Lemmas 4–5 and §5 (claim F17)

import Definitions.Def_Plasticity_Faces
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.Faces
theorem exists_isCompact_boundary_preimage_subset {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hbij : Set.BijOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (C : Set Y) (hC : IsSphereFace C) (hfin : FiniteDimensional ℝ (vectorSpan ℝ C))
    (ih : ∀ C' : Set Y, IsSphereFace C' → C' ⊆ C →
      Module.finrank ℝ (vectorSpan ℝ C') < Module.finrank ℝ (vectorSpan ℝ C) → MatchesFace F C') :
    ∃ K : Set X, IsCompact K ∧ Metric.closedBall (0 : X) 1 ∩ F ⁻¹' (intrinsicFrontier ℝ C) ⊆ K := by sorry
end Plasticity.Faces
