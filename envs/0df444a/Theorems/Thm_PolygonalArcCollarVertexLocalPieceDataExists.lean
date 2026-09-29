-- Prove2me | Theorems.Thm_PolygonalArcCollarVertexLocalPieceDataExists
-- name    : PolygonalArcCollarVertexLocalPieceDataExists
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-28T04:12:30.764996+00:00
-- url     : https://prove2.me/theorems/2f646d30-5ea9-4967-8b39-d65a9b0e2557
-- title:
--   Existence of polygonal-arc collar vertex-local piece data
-- statement:
--   For a polygonal arc with control radii, middle-segment data, forbidden margins, and separated tube data, there exists a vertex-local-piece datum. The datum supplies the vertex disks, endpoint pieces, left and right local pieces, attachment sets, and their structural interface fields.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarVertexLocalPieceDataExists.lean#L1-582

import Definitions.Def_PolygonalArcCollarVertexLocalPieceData

open Classical
noncomputable section

set_option maxHeartbeats 1200000

lemma PolygonalArcCollarVertexLocalPieceDataExists (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (separatedTubes :
      PolygonalArcCollarSeparatedTubeData γ controlRadii middleSegments
        forbiddenMargins) :
    Nonempty
      (PolygonalArcCollarVertexLocalPieceData γ controlRadii middleSegments
        forbiddenMargins separatedTubes) := by sorry
