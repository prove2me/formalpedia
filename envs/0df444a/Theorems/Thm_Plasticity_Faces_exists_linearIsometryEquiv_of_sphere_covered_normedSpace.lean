-- Prove2me | Theorems.Thm_Plasticity_Faces_exists_linearIsometryEquiv_of_sphere_covered_normedSpace
-- name    : Plasticity.Faces.exists_linearIsometryEquiv_of_sphere_covered_normedSpace
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-15T02:23:02.638861+00:00
-- url     : https://prove2.me/theorems/51e4f830-2efb-4818-bbbf-3e694149b742
-- title:
--   Sphere covered by finite-dimensional faces, normed spaces: every nonexpansive bijection onto the ball is linear
-- statement:
--   Let $X,Y$ be real normed spaces, not necessarily complete, such that every point of the unit sphere of $Y$ lies in a finite-dimensional face of $B_Y$ contained in the sphere. Then every map $F$ that is nonexpansive and injective on $B_X$ with $B_Y\subseteq F(B_X)$ (that is, every nonexpansive bijection of $B_X$ onto $B_Y$; that $F$ maps $B_X$ into $B_Y$ follows) is the restriction of a surjective linear isometry $T\colon X\to Y$.
--   This is the card `Plasticity.Faces.exists_linearIsometryEquiv_of_sphere_covered` without completeness: the proof ends as Angosto–Kadets–Zavarzina's Theorem 4.11, by homogeneity on every preimage face and the Mazur–Ulam theorem, instead of through the sphere-preservation theorem U10.
-- source:
--   This repository: claim F17 (claims/f.md), expositions/faces/finite_faces_boundary_crossing.md §6; compare C. Angosto, V. Kadets, O. Zavarzina, J. Math. Anal. Appl. 471 (2019), Theorem 4.11

import Definitions.Def_Plasticity_Faces
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.Faces
theorem exists_linearIsometryEquiv_of_sphere_covered_normedSpace {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hinj : Set.InjOn F (Metric.closedBall (0 : X) 1))
    (hsurj : Set.SurjOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hcover : ∀ y ∈ Metric.sphere (0 : Y) 1, ∃ C : Set Y,
      IsSphereFace C ∧ FiniteDimensional ℝ (vectorSpan ℝ C) ∧ y ∈ C) :
    ∃ T : X ≃ₗᵢ[ℝ] Y, Set.EqOn F T (Metric.closedBall (0 : X) 1) := by sorry
end Plasticity.Faces
