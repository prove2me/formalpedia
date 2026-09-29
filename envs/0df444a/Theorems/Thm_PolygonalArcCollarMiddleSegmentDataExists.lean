-- Prove2me | Theorems.Thm_PolygonalArcCollarMiddleSegmentDataExists
-- name    : PolygonalArcCollarMiddleSegmentDataExists
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T23:55:01.174985+00:00
-- url     : https://prove2.me/theorems/2451bfdb-1728-4351-9fd1-3de54da156ad
-- title:
--   PolygonalArcCollarMiddleSegmentDataExists
-- statement:
--   For every polygonal arc and collar-control radii, there exists middle-segment data selecting nonempty compact subsegments of all edges with the prescribed parameter and neighborhood properties.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarMiddleSegmentDataExists.lean#L1-133

import Definitions.Def_PolygonalArcCollarMiddleSegmentData

open Classical
noncomputable section

lemma PolygonalArcCollarMiddleSegmentDataExists (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η) :
    Nonempty (PolygonalArcCollarMiddleSegmentData γ controlRadii) := by sorry
