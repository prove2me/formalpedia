-- Prove2me | Theorems.Thm_Plasticity_Faces_matchesFace_of_boundary_preimage_relativelyCompact
-- name    : Plasticity.Faces.matchesFace_of_boundary_preimage_relativelyCompact
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-15T00:33:57.425927+00:00
-- url     : https://prove2.me/theorems/017b677b-7037-4fc0-bb5a-bc9af40084a6
-- title:
--   A face whose boundary preimage is relatively compact is carried onto a face of the same dimension
-- statement:
--   Let $X,Y$, $F$ and $C$ be as in the card `Plasticity.Faces.matchesFace_of_finiteDimensional`, with $\dim C=n$, suppose that every face $C'\subseteq C$ of $B_Y$ contained in the sphere with $\dim C'<n$ satisfies `MatchesFace F C'`, and suppose that the preimage $B_X\cap F^{-1}(\partial C)$ of the relative boundary of $C$ lies in a compact set. Then $C$ satisfies `MatchesFace F C`: $D=B_X\cap F^{-1}(C)$ is a compact face of the same dimension, $B_X\cap F^{-1}(-C)=-D$, boundaries and extreme points correspond, and $F(tD)=tC$ for $0\le t\le1$.
--   The proof uses invariance of domain (a cone over the compact boundary preimage) and the non-contractibility of spheres (no retraction of a ball onto its boundary).
-- source:
--   This repository: expositions/faces/codirected_compactness.md, Lemma 2 and Propositions 3–4 (claim F11)

import Definitions.Def_Plasticity_Faces
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.Faces
theorem matchesFace_of_boundary_preimage_relativelyCompact {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hbij : Set.BijOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (C : Set Y) (hC : IsSphereFace C) (hfin : FiniteDimensional ℝ (vectorSpan ℝ C))
    (ih : ∀ C' : Set Y, IsSphereFace C' → C' ⊆ C →
      Module.finrank ℝ (vectorSpan ℝ C') < Module.finrank ℝ (vectorSpan ℝ C) → MatchesFace F C')
    (htame : ∃ K : Set X, IsCompact K ∧
      Metric.closedBall (0 : X) 1 ∩ F ⁻¹' (intrinsicFrontier ℝ C) ⊆ K) :
    MatchesFace F C := by sorry
end Plasticity.Faces
