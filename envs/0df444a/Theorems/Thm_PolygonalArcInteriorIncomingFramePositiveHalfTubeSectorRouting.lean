-- Prove2me | Theorems.Thm_PolygonalArcInteriorIncomingFramePositiveHalfTubeSectorRouting
-- name    : PolygonalArcInteriorIncomingFramePositiveHalfTubeSectorRouting
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T18:41:07.82754+00:00
-- url     : https://prove2.me/theorems/f53d55e0-fc45-481e-9a9f-c637a260e7a7
-- title:
--   Polygonal Arc Interior Incoming Frame Positive Half Tube Sector Routing
-- statement:
--   Let $\gamma$ be a polygonal arc with collar control radii, middle segments,
--   forbidden margins, and compatible oriented tube data.  Fix consecutive
--   segments
--   $[p_j,p_{j+1}]$ and $[p_{j+1},p_{j+2}]$.  Put
--   $$
--     p=p_{j+1},\qquad u=p_j-p_{j+1}.
--   $$
--   Assume that, in the incoming outward frame, the outgoing direction satisfies
--   $$
--     p_{j+2}-p_{j+1}
--       =c\,u+s\,\operatorname{rot}_{90}(u),
--     \qquad s>0\quad\text{or}\quad (s=0\text{ and }c<0).
--   $$
--   Let
--   $$
--     \Phi(z)=p+z_0u+z_1\operatorname{rot}_{90}(u),
--     \qquad
--     C=B\!\left(0,\frac{r_{j+1}}{\|u\|}\right),
--   $$
--   and let
--   $$
--     R=\{z\in C:\ z_1<0
--         \text{ or } c z_1-s z_0>0\}.
--   $$
--   Then the positive half-tube on the incoming segment and the positive
--   half-tube on the outgoing segment, wherever they lie in $\Phi(C)$, both
--   lie in the transported sector $\Phi(R)$:
--   $$
--     S.\operatorname{leftHalf}_j\cap\Phi(C)\subseteq \Phi(R),
--     \qquad
--     S.\operatorname{leftHalf}_{j+1}\cap\Phi(C)\subseteq \Phi(R),
--   $$
--   where $S$ is the separated-tube datum underlying the compatible oriented
--   tubes.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PolygonalArcInteriorIncomingFramePositiveHalfTubeSectorRouting`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcInteriorIncomingFramePositiveHalfTubeSectorRouting.lean#L1-L152

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Definitions.Def_PlanarRot90
import Definitions.Def_PolygonalArc
import Definitions.Def_PolygonalArcCollarCompatibleOrientedTubeData
import Definitions.Def_PolygonalArcCollarControlRadii
import Definitions.Def_PolygonalArcCollarMiddleForbiddenMargins
import Definitions.Def_PolygonalArcCollarMiddleSegmentData

open Set
open Classical
noncomputable section

lemma PolygonalArcInteriorIncomingFramePositiveHalfTubeSectorRouting
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (compatibleTubes :
      PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (j : ℕ) (hj : j + 1 < γ.vertices.length)
    (hnext : (j + 1) + 1 < γ.vertices.length)
    (c s : ℝ)
    (hrep : γ.vertices[j + 2] - γ.vertices[j + 1] =
      c • (γ.vertices[j] - γ.vertices[j + 1]) +
        s • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]))
    (hpos : 0 < s ∨ s = 0 ∧ c < 0) :
    let sep :=
      compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData
    let p : EuclideanSpace ℝ (Fin 2) := γ.vertices[j + 1]
    let u : EuclideanSpace ℝ (Fin 2) := γ.vertices[j] - γ.vertices[j + 1]
    let rho : ℝ := controlRadii.radius ⟨j + 1, hj⟩
    let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => p + z 0 • u + z 1 • PlanarRot90 u
    let C : Set (EuclideanSpace ℝ (Fin 2)) :=
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (rho / ‖u‖)
    let R : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | z ∈ C ∧ (z 1 < 0 ∨ 0 < c * z 1 - s * z 0)}
    sep.leftHalf j hj ∩ chart '' C ⊆ chart '' R ∧
      sep.leftHalf (j + 1) hnext ∩ chart '' C ⊆ chart '' R := by sorry
