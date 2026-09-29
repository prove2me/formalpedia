-- Prove2me | Theorems.Thm_PolygonalArcCollarLocalTopologyDataExists
-- name    : PolygonalArcCollarLocalTopologyDataExists
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-28T04:12:22.069115+00:00
-- url     : https://prove2.me/theorems/45828523-d3f4-4795-90be-38859d827b4a
-- title:
--   Existence of polygonal-arc collar local-topology data
-- statement:
--   For a polygonal arc equipped with control radii, middle-segment data, forbidden margins, compatible oriented tubes, and vertex-local pieces, a local-topology datum exists. The datum has exactly the supplied collar, side-piece, germ, attachment, connectivity, disjointness, and endpoint-interface fields of `PolygonalArcCollarLocalTopologyData`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarLocalTopologyDataExists.lean#L1-2645

import Definitions.Def_PolygonalArcCollarLocalTopologyData

open Classical
noncomputable section

set_option maxHeartbeats 1800000

lemma PolygonalArcCollarLocalTopologyDataExists (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (compatibleTubes :
      PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (vertexLocalPieces :
      PolygonalArcCollarVertexLocalPieceData γ controlRadii middleSegments
        forbiddenMargins
        compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData) :
    Nonempty
      (PolygonalArcCollarLocalTopologyData γ controlRadii middleSegments
        forbiddenMargins compatibleTubes vertexLocalPieces) := by sorry
