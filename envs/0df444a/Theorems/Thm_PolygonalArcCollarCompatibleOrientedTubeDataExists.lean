-- Prove2me | Theorems.Thm_PolygonalArcCollarCompatibleOrientedTubeDataExists
-- name    : PolygonalArcCollarCompatibleOrientedTubeDataExists
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-28T00:31:21.839727+00:00
-- url     : https://prove2.me/theorems/117a92d1-6c89-439d-a9b3-5a46b9a3f805
-- title:
--   Existence of compatible oriented tube data
-- statement:
--   For a polygonal arc with fixed control radii, middle segments, and middle forbidden margins, there exists compatible oriented tube data satisfying all of the structural, separation, and cone-compatibility fields in its definition.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarCompatibleOrientedTubeDataExists.lean#L1-L20

import Definitions.Def_PolygonalArcCollarCompatibleOrientedTubeData

open Classical
noncomputable section

lemma PolygonalArcCollarCompatibleOrientedTubeDataExists (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments) :
    Nonempty
      (PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins) := by sorry
