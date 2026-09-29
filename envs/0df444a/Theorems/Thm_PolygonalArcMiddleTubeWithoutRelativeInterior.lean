-- Prove2me | Theorems.Thm_PolygonalArcMiddleTubeWithoutRelativeInterior
-- name    : PolygonalArcMiddleTubeWithoutRelativeInterior
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-28T05:03:25.232878+00:00
-- url     : https://prove2.me/theorems/774a2996-ab1d-46c7-beed-46e8682a3c06
-- title:
--   Middle tube minus relative interior splits into oriented halves
-- statement:
--   For each middle segment, removing the polygonal arc's relative interior from the corresponding open tube leaves exactly the union of its positive and negative oriented half-tubes. Thus the two half-tubes give the two sides of the tube away from the arc.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcMiddleTubeWithoutRelativeInterior.lean#L1-L26

import Definitions.Def_PolygonalArcCollarLocalSideData

open Classical
noncomputable section

lemma PolygonalArcMiddleTubeWithoutRelativeInterior
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
        forbiddenMargins orientedTubes vertexLocalPieces)
    (j : ℕ) (hj : j + 1 < γ.vertices.length) :
    orientedTubes.toPolygonalArcCollarSeparatedTubeData.tube j hj \ γ.relativeInterior =
      orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf j hj ∪
        orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf j hj := by sorry
