-- Prove2me | Theorems.Thm_Plasticity_Faces_matchesFace_of_finiteDimensional
-- name    : Plasticity.Faces.matchesFace_of_finiteDimensional
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-15T00:31:30.698825+00:00
-- url     : https://prove2.me/theorems/d9884712-a5d5-47bc-b843-925d267b06d1
-- title:
--   Every finite-dimensional face of the target ball is carried onto a face of the same dimension
-- statement:
--   Let $X,Y$ be real normed spaces, $F\colon B_X\to B_Y$ a nonexpansive bijection, and $C$ a finite-dimensional face of $B_Y$ contained in the unit sphere. Put $D=B_X\cap F^{-1}(C)$, the preimage of $C$. Then $D$ is a compact face of $B_X$ contained in the unit sphere, of the same dimension as $C$, and
--   $$B_X\cap F^{-1}(-C)=-D,\qquad B_X\cap F^{-1}(\partial C)=\partial D,\qquad B_X\cap F^{-1}(\operatorname{ext}C)=\operatorname{ext}D,\qquad F(tD)=tC\quad(0\le t\le1),$$
--   where $\partial$ is the relative boundary and $\operatorname{ext}$ the set of extreme points. No completeness, continuity of $F^{-1}$, strict convexity, polyhedrality or separability is assumed.
-- source:
--   This repository: claim F17 (claims/f.md), Theorem 1 of expositions/faces/finite_faces_boundary_crossing.md, with Propositions 3–4 of expositions/faces/codirected_compactness.md (claim F11); the polytope case is in C. Angosto, V. Kadets, O. Zavarzina, J. Math. Anal. Appl. 471 (2019), Theorem 4.8 (arXiv:1808.08534)

import Definitions.Def_Plasticity_Faces
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.Faces
open scoped Pointwise
theorem matchesFace_of_finiteDimensional {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hbij : Set.BijOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (C : Set Y) (hC : IsSphereFace C) (hfin : FiniteDimensional ℝ (vectorSpan ℝ C))
    (D : Set X) (hD : D = Metric.closedBall (0 : X) 1 ∩ F ⁻¹' C) :
    IsSphereFace D ∧ IsCompact D ∧ FiniteDimensional ℝ (vectorSpan ℝ D) ∧
    Module.finrank ℝ (vectorSpan ℝ D) = Module.finrank ℝ (vectorSpan ℝ C) ∧
    Metric.closedBall (0 : X) 1 ∩ F ⁻¹' (-C) = -D ∧
    Metric.closedBall (0 : X) 1 ∩ F ⁻¹' (intrinsicFrontier ℝ C) = intrinsicFrontier ℝ D ∧
    Metric.closedBall (0 : X) 1 ∩ F ⁻¹' (C.extremePoints ℝ) = D.extremePoints ℝ ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1, F '' (t • D) = t • C := by sorry
end Plasticity.Faces
