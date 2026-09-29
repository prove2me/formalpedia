-- Prove2me | Theorems.Thm_PolygonalArcSideStripAssembly
-- name    : PolygonalArcSideStripAssembly
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T23:55:39.632986+00:00
-- url     : https://prove2.me/theorems/2cd45c26-3c4d-4357-8929-64986fea76a4
-- title:
--   PolygonalArcSideStripAssembly
-- statement:
--   Given oriented separated tubes and compatible vertex-local and side data for a polygonal arc, there exists polygonal side-strip data whose collar, left strip, and right strip are the corresponding unions and whose collar lies within the prescribed neighborhood of the arc.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcSideStripAssembly.lean#L1-664

import Definitions.Def_PolygonalArcCollarLocalSideData
import Definitions.Def_PolygonalSideStrips

import Mathlib.Tactic

open Classical
open Filter
noncomputable section

lemma PolygonalArcSideStripAssembly (γ : PolygonalArc) {η : ℝ}
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
