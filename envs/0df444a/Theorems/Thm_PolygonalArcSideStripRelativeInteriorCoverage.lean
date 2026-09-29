-- Prove2me | Theorems.Thm_PolygonalArcSideStripRelativeInteriorCoverage
-- name    : PolygonalArcSideStripRelativeInteriorCoverage
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-28T05:03:26.660663+00:00
-- url     : https://prove2.me/theorems/98f28d80-924d-40ec-9ffc-d4301bf0b055
-- title:
--   Side-strip collar covers the polygonal arc relative interior
-- statement:
--   The relative interior of a polygonal arc is covered by the union of all middle tubes and all vertex collars associated with the collar data. This is the coverage statement needed to make the assembled collar contain the whole relative interior.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcSideStripRelativeInteriorCoverage.lean#L1-L25

import Definitions.Def_PolygonalArcCollarLocalSideData

open Classical
noncomputable section

lemma PolygonalArcSideStripRelativeInteriorCoverage
    (γ : PolygonalArc) {η : ℝ}
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
    γ.relativeInterior ⊆
      ((⋃ (j : ℕ), ⋃ (hj : j + 1 < γ.vertices.length),
          orientedTubes.toPolygonalArcCollarSeparatedTubeData.tube j hj) ∪
        (⋃ i : Fin γ.vertices.length, localSideData.vertexCollar i)) := by sorry
