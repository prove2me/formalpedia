-- Prove2me | Theorems.Thm_PolygonalArcSideStripAssemblyBundled
-- name    : PolygonalArcSideStripAssemblyBundled
-- status  : Open
-- author  : @moona3k
-- created : 2026-10-04T21:04:49.926613+00:00
-- url     : https://prove2.me/theorems/1a807ea1-46e6-46bd-80de-a605f2270774
-- title:
--   Polygonal Arc Side Strip Assembly Bundled
-- statement:
--   Let $\gamma$ be a polygonal arc, let $\eta$ be a collar scale, and fix
--   control radii, middle segments, forbidden middle margins, oriented separated
--   middle tubes, vertex-local attachment data, and collar local-side data for
--   $\gamma$.  Write the separated middle tubes as
--   $$
--     T_j,\qquad T_j^+,\qquad T_j^- ,
--   $$
--   and write the vertex collar and side pieces as
--   $$
--     C_i,\qquad L_i,\qquad R_i .
--   $$
--   Define
--   $$
--     C=\Bigl(\bigcup_j T_j\Bigr)\cup\Bigl(\bigcup_i C_i\Bigr),\quad
--     L=\Bigl(\bigcup_j T_j^+\Bigr)\cup\Bigl(\bigcup_i L_i\Bigr),\quad
--     R=\Bigl(\bigcup_j T_j^-\Bigr)\cup\Bigl(\bigcup_i R_i\Bigr),
--   $$
--   where $j$ ranges over listed segments and $i$ over listed vertices.  Then
--   there is side-strip data $S$ for $\gamma$ whose collar, left strip, and
--   right strip are respectively $C,L,R$.  Moreover every point of $S$'s
--   collar lies within distance $<\eta$ of some point of
--   $\gamma.\mathrm{carrier}$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PolygonalArcSideStripAssemblyBundled`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcSideStripAssembly.lean#L1-L664

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_PlaneFaceData
import Definitions.Def_PolygonalArc
import Definitions.Def_PolygonalArcCollarControlRadii
import Definitions.Def_PolygonalArcCollarLocalSideData
import Definitions.Def_PolygonalArcCollarMiddleForbiddenMargins
import Definitions.Def_PolygonalArcCollarMiddleSegmentData
import Definitions.Def_PolygonalArcCollarOrientedSeparatedTubeData
import Definitions.Def_PolygonalArcCollarVertexLocalPieceData

open Classical
open Filter
noncomputable section

lemma PolygonalArcSideStripAssemblyBundled (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (orientedTubes :
      PolygonalArcCollarOrientedSeparatedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (vertexLocalPieces :
      PolygonalArcCollarVertexLocalPieceData γ controlRadii middleSegments
        forbiddenMargins orientedTubes.toPolygonalArcCollarSeparatedTubeData)
    (localSideData :
      PolygonalArcCollarLocalSideData γ controlRadii middleSegments
        forbiddenMargins orientedTubes vertexLocalPieces) :
    ∃ S : PolygonalSideStrips γ,
      S.collar =
          ((⋃ (j : ℕ), ⋃ (hj : j + 1 < γ.vertices.length),
              orientedTubes.toPolygonalArcCollarSeparatedTubeData.tube j hj) ∪
            (⋃ i : Fin γ.vertices.length, localSideData.vertexCollar i)) ∧
        S.leftStrip =
          ((⋃ (j : ℕ), ⋃ (hj : j + 1 < γ.vertices.length),
              orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf j hj) ∪
            (⋃ i : Fin γ.vertices.length, localSideData.leftSidePiece i)) ∧
        S.rightStrip =
          ((⋃ (j : ℕ), ⋃ (hj : j + 1 < γ.vertices.length),
              orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf j hj) ∪
            (⋃ i : Fin γ.vertices.length, localSideData.rightSidePiece i)) ∧
        ∀ z ∈ S.collar, ∃ p ∈ γ.carrier, dist z p < η := by sorry
