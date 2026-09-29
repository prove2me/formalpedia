-- Prove2me | Theorems.Thm_PolygonalArcCollarLocalSideDataOfLocalTopologyData
-- name    : PolygonalArcCollarLocalSideDataOfLocalTopologyData
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-28T03:41:53.994766+00:00
-- url     : https://prove2.me/theorems/18b01235-34f7-42d9-8cb7-286595d4699a
-- title:
--   Local side data from local-topology data
-- statement:
--   Given a polygonal arc, its collar parameters, compatible oriented tubes, vertex-local pieces, and a local-topology datum, there exists local side data on the same vertex collars and side pieces. For every vertex index, the resulting vertex collar, left side piece, and right side piece are exactly the corresponding sets in the supplied local-topology datum. This packages the local-topology interface into the local-side-data structure while preserving all of its set-valued components.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarLocalSideDataOfLocalTopologyData.lean#L1-34

import Definitions.Def_PolygonalArcCollarLocalSideData
import Definitions.Def_PolygonalArcCollarLocalTopologyData

open Classical
noncomputable section

set_option maxHeartbeats 1200000

lemma PolygonalArcCollarLocalSideDataOfLocalTopologyData (γ : PolygonalArc) {η : ℝ}
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
        compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData)
    (localTopology :
      PolygonalArcCollarLocalTopologyData γ controlRadii middleSegments
        forbiddenMargins compatibleTubes vertexLocalPieces) :
    ∃ localSideData :
      PolygonalArcCollarLocalSideData γ controlRadii middleSegments
        forbiddenMargins compatibleTubes.orientedTubes vertexLocalPieces,
      (∀ i : Fin γ.vertices.length,
        localSideData.vertexCollar i = localTopology.vertexCollar i) ∧
        (∀ i : Fin γ.vertices.length,
          localSideData.leftSidePiece i = localTopology.leftSidePiece i) ∧
          (∀ i : Fin γ.vertices.length,
            localSideData.rightSidePiece i = localTopology.rightSidePiece i) := by sorry
