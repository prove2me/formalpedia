-- Prove2me | Theorems.Thm_PolygonalArcInteriorIncomingFrameSignedHalfTubeSectorRouting
-- name    : PolygonalArcInteriorIncomingFrameSignedHalfTubeSectorRouting
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T18:41:11.895171+00:00
-- url     : https://prove2.me/theorems/30db5d08-1f64-414e-91c8-fb5ba5e9f2ed
-- title:
--   Polygonal Arc Interior Incoming Frame Signed Half Tube Sector Routing
-- statement:
--   Let $\gamma$ be a polygonal arc with collar control radii, middle
--   segments, forbidden margins, and compatible oriented tube data.  Fix
--   consecutive listed segments
--   $[p_j,p_{j+1}]$ and $[p_{j+1},p_{j+2}]$.  Put
--   $$
--     p=p_{j+1},\qquad u=p_j-p_{j+1},
--   $$
--   and suppose that in the incoming outward frame
--   $$
--     p_{j+2}-p_{j+1}
--       =c\,u+s\,\operatorname{rot}_{90}(u),
--     \qquad s>0\quad\hbox{or}\quad (s=0\hbox{ and }c<0).
--   $$
--   Let
--   $$
--     \Phi(z)=p+z_0u+z_1\operatorname{rot}_{90}(u),\qquad
--     C=B\!\left(0,\frac{r_{j+1}}{\|u\|}\right),
--   $$
--   and assume that $\Phi(C)=B(p,r_{j+1})$, as supplied by the transported
--   two-ray sector chart.  Define
--   $$
--     L=\{z\in C:\ 0<z_1,\ c z_1-sz_0<0\},\qquad
--     R=\{z\in C:\ z_1<0\ {\rm or}\ 0<c z_1-sz_0\}.
--   $$
--   Then, after intersecting with the bend ball $B(p,r_{j+1})$, the positive
--   half-tubes on the incoming and outgoing incident segments lie in
--   $\Phi(R)$, and the negative half-tubes on the incoming and outgoing
--   incident segments lie in $\Phi(L)$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PolygonalArcInteriorIncomingFrameSignedHalfTubeSectorRouting`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcInteriorIncomingFrameSignedHalfTubeSectorRouting.lean#L1-L487

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

lemma PolygonalArcInteriorIncomingFrameSignedHalfTubeSectorRouting
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
    (hpos : 0 < s ∨ s = 0 ∧ c < 0)
    (hCeq :
      let p : EuclideanSpace ℝ (Fin 2) := γ.vertices[j + 1]
      let u : EuclideanSpace ℝ (Fin 2) := γ.vertices[j] - γ.vertices[j + 1]
      let rho : ℝ := controlRadii.radius ⟨j + 1, hj⟩
      let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
        fun z => p + z 0 • u + z 1 • PlanarRot90 u
      let C : Set (EuclideanSpace ℝ (Fin 2)) :=
        Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (rho / ‖u‖)
      chart '' C = Metric.ball p rho) :
    let sep :=
      compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData
    let p : EuclideanSpace ℝ (Fin 2) := γ.vertices[j + 1]
    let u : EuclideanSpace ℝ (Fin 2) := γ.vertices[j] - γ.vertices[j + 1]
    let rho : ℝ := controlRadii.radius ⟨j + 1, hj⟩
    let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => p + z 0 • u + z 1 • PlanarRot90 u
    let C : Set (EuclideanSpace ℝ (Fin 2)) :=
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (rho / ‖u‖)
    let L : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | z ∈ C ∧ 0 < z 1 ∧ c * z 1 - s * z 0 < 0}
    let R : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | z ∈ C ∧ (z 1 < 0 ∨ 0 < c * z 1 - s * z 0)}
    sep.leftHalf j hj ∩ Metric.ball p rho ⊆ chart '' R ∧
      sep.leftHalf (j + 1) hnext ∩ Metric.ball p rho ⊆ chart '' R ∧
      sep.rightHalf j hj ∩ Metric.ball p rho ⊆ chart '' L ∧
      sep.rightHalf (j + 1) hnext ∩ Metric.ball p rho ⊆ chart '' L := by sorry
