-- Prove2me | Theorems.Thm_Plasticity_Faces_isCompact_and_eq_closedBall_inter_affineSpan
-- name    : Plasticity.Faces.isCompact_and_eq_closedBall_inter_affineSpan
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-15T00:33:58.868165+00:00
-- url     : https://prove2.me/theorems/e9097ee1-2c59-4a57-b08c-b263ce0b25b7
-- title:
--   A finite-dimensional face of the unit ball is compact and is the ball's trace on its affine hull
-- statement:
--   Let $C$ be a face of the closed unit ball $B$ of a real normed space contained in the unit sphere, with finite-dimensional affine hull. Then $C=B\cap\operatorname{aff}C$; in particular $C$ is closed, and it is compact.
--   Proof: for $c$ in the relative interior of $C$ and $z\in B\cap\operatorname{aff}C$, the point $c+\varepsilon(c-z)$ lies in $C$ for small $\varepsilon>0$, and the face property at $c$ puts $z$ in $C$.
-- source:
--   This repository: expositions/faces/abstract_lenses.md §2, display (2.2) (claim F12); expositions/faces/finite_faces_boundary_crossing.md §1

import Definitions.Def_Plasticity_Faces

namespace Plasticity.Faces
theorem isCompact_and_eq_closedBall_inter_affineSpan {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (hC : IsSphereFace C) (hfin : FiniteDimensional ℝ (vectorSpan ℝ C)) :
    IsCompact C ∧ C = Metric.closedBall (0 : E) 1 ∩ (affineSpan ℝ C : Set E) := by sorry
end Plasticity.Faces
