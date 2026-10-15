-- Prove2me | Theorems.Thm_Plasticity_Faces_hasPlasticUnitBall_of_sphere_covered
-- name    : Plasticity.Faces.hasPlasticUnitBall_of_sphere_covered
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-15T00:31:58.712824+00:00
-- url     : https://prove2.me/theorems/e03917d0-630c-4554-b21a-b2680912da83
-- title:
--   A ball whose sphere is covered by finite-dimensional faces is plastic
-- statement:
--   Let $X$ be a real Banach space such that every point of its unit sphere lies in a finite-dimensional face of the closed unit ball $B_X$ contained in the sphere. Then $B_X$ is plastic: every nonexpansive bijection of $B_X$ onto itself is an isometry.
-- source:
--   This repository: claim F17 (claims/f.md), last sentence; the case X = Y of the card Plasticity.Faces.exists_linearIsometryEquiv_of_sphere_covered

import Definitions.Def_Plasticity_Basic
import Definitions.Def_Plasticity_Faces

namespace Plasticity.Faces
theorem hasPlasticUnitBall_of_sphere_covered {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hcover : ∀ x ∈ Metric.sphere (0 : X) 1, ∃ C : Set X,
      IsSphereFace C ∧ FiniteDimensional ℝ (vectorSpan ℝ C) ∧ x ∈ C) :
    HasPlasticUnitBall X := by sorry
end Plasticity.Faces
