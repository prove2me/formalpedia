-- Prove2me | Theorems.Thm_Plasticity_Faces_exists_linearIsometryEquiv_of_sphere_covered
-- name    : Plasticity.Faces.exists_linearIsometryEquiv_of_sphere_covered
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-15T00:31:44.157823+00:00
-- url     : https://prove2.me/theorems/12aa7b1c-133e-49e4-9c1e-633fa4830910
-- title:
--   Sphere covered by finite-dimensional faces: every nonexpansive bijection onto the ball is linear
-- statement:
--   Let $X,Y$ be real Banach spaces such that every point of the unit sphere of $Y$ lies in a finite-dimensional face of $B_Y$ contained in the sphere. Then every nonexpansive bijection $F\colon B_X\to B_Y$ is the restriction of a surjective linear isometry $T\colon X\to Y$.
--   This removes the polyhedrality hypothesis from Theorem 4.11 of Angosto, Kadets and Zavarzina, where the sphere is a union of finite-dimensional polyhedral extreme subsets.
-- source:
--   This repository: claim F17 (claims/f.md), Corollary 3 of expositions/faces/finite_faces_boundary_crossing.md, through §6 of expositions/faces/codirected_compactness.md (claim F11) and the sphere-preservation theorem U10; compare C. Angosto, V. Kadets, O. Zavarzina, J. Math. Anal. Appl. 471 (2019), Theorem 4.11

import Definitions.Def_Plasticity_Faces
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.Faces
theorem exists_linearIsometryEquiv_of_sphere_covered {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (F : X → Y)
    (hbij : Set.BijOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hcover : ∀ y ∈ Metric.sphere (0 : Y) 1, ∃ C : Set Y,
      IsSphereFace C ∧ FiniteDimensional ℝ (vectorSpan ℝ C) ∧ y ∈ C) :
    ∃ T : X ≃ₗᵢ[ℝ] Y, Set.EqOn F T (Metric.closedBall (0 : X) 1) := by sorry
end Plasticity.Faces
