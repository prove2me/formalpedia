-- Prove2me | Theorems.Thm_PolygonalArcInteriorOutgoingFrameSignedHalfTubeSectorRouting
-- name    : PolygonalArcInteriorOutgoingFrameSignedHalfTubeSectorRouting
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T18:41:22.608748+00:00
-- url     : https://prove2.me/theorems/08b93372-dba6-4b84-88c9-8b328e434290
-- title:
--   Polygonal Arc Interior Outgoing Frame Signed Half Tube Sector Routing
-- statement:
--   Let $\gamma$ be a polygonal arc with collar control radii, middle
--   segments, forbidden margins, and compatible oriented tube data.  Fix
--   consecutive listed segments
--   $[p_j,p_{j+1}]$ and $[p_{j+1},p_{j+2}]$.  Put
--   $$
--     p=p_{j+1},\qquad v=p_{j+2}-p_{j+1},
--   $$
--   and suppose that the incoming outward direction is represented in the
--   outgoing frame by
--   $$
--     p_j-p_{j+1}=c\,v+s\,\operatorname{rot}_{90}(v),\qquad s>0.
--   $$
--   Let
--   $$
--     \Phi(z)=p+z_0v+z_1\operatorname{rot}_{90}(v),\qquad
--     C=B\!\left(0,\frac{r_{j+1}}{\|v\|}\right),
--   $$
--   and assume that $\Phi(C)=B(p,r_{j+1})$, as supplied by the transported
--   two-ray sector chart.  Define
--   $$
--     L=\{z\in C:\ 0<z_1,\ c z_1-sz_0<0\},\qquad
--     R=\{z\in C:\ z_1<0\ {\rm or}\ 0<c z_1-sz_0\}.
--   $$
--   Then, after intersecting with the bend ball $B(p,r_{j+1})$, the positive
--   half-tubes on the incoming and outgoing incident segments lie in
--   $\Phi(L)$, and the negative half-tubes on the incoming and outgoing
--   incident segments lie in $\Phi(R)$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PolygonalArcInteriorOutgoingFrameSignedHalfTubeSectorRouting`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcInteriorOutgoingFrameSignedHalfTubeSectorRouting.lean#L1-L519

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Analysis.Convex.PathConnected
import Definitions.Def_PlanarRot90
import Definitions.Def_PolygonalArc
import Definitions.Def_PolygonalArcCollarCompatibleOrientedTubeData
import Definitions.Def_PolygonalArcCollarControlRadii
import Definitions.Def_PolygonalArcCollarMiddleForbiddenMargins
import Definitions.Def_PolygonalArcCollarMiddleSegmentData

open Set
open Classical
noncomputable section

lemma PolygonalArcInteriorOutgoingFrameSignedHalfTubeSectorRouting
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
    (hrep : γ.vertices[j] - γ.vertices[j + 1] =
      c • (γ.vertices[j + 2] - γ.vertices[j + 1]) +
        s • PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1]))
    (hpos : 0 < s)
    (hCeq :
      let p : EuclideanSpace ℝ (Fin 2) := γ.vertices[j + 1]
      let v : EuclideanSpace ℝ (Fin 2) := γ.vertices[j + 2] - γ.vertices[j + 1]
      let rho : ℝ := controlRadii.radius ⟨j + 1, hj⟩
      let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
        fun z => p + z 0 • v + z 1 • PlanarRot90 v
      let C : Set (EuclideanSpace ℝ (Fin 2)) :=
        Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (rho / ‖v‖)
      chart '' C = Metric.ball p rho) :
    let sep :=
      compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData
    let p : EuclideanSpace ℝ (Fin 2) := γ.vertices[j + 1]
    let v : EuclideanSpace ℝ (Fin 2) := γ.vertices[j + 2] - γ.vertices[j + 1]
    let rho : ℝ := controlRadii.radius ⟨j + 1, hj⟩
    let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => p + z 0 • v + z 1 • PlanarRot90 v
    let C : Set (EuclideanSpace ℝ (Fin 2)) :=
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (rho / ‖v‖)
    let L : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | z ∈ C ∧ 0 < z 1 ∧ c * z 1 - s * z 0 < 0}
    let R : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | z ∈ C ∧ (z 1 < 0 ∨ 0 < c * z 1 - s * z 0)}
    sep.leftHalf j hj ∩ Metric.ball p rho ⊆ chart '' L ∧
      sep.leftHalf (j + 1) hnext ∩ Metric.ball p rho ⊆ chart '' L ∧
      sep.rightHalf j hj ∩ Metric.ball p rho ⊆ chart '' R ∧
      sep.rightHalf (j + 1) hnext ∩ Metric.ball p rho ⊆ chart '' R := by sorry
