-- Prove2me | Theorems.Thm_PolygonalArcCollarMiddleForbiddenMarginsExists
-- name    : PolygonalArcCollarMiddleForbiddenMarginsExists
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T23:54:56.721196+00:00
-- url     : https://prove2.me/theorems/78befe2c-7e83-4fba-962b-ab809127be44
-- title:
--   PolygonalArcCollarMiddleForbiddenMarginsExists
-- statement:
--   For every polygonal arc, collar-control radii, and middle-segment data, there exists a family of positive forbidden margins separating each middle segment from nonadjacent edges, nonincident control disks, and nonadjacent middle cores.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarMiddleForbiddenMarginsExists.lean#L1-250

import Definitions.Def_PolygonalArcCollarMiddleForbiddenMargins

import Mathlib.Analysis.Normed.Module.Convex

open Classical
noncomputable section

lemma PolygonalArcCollarMiddleForbiddenMarginsExists (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii) :
    Nonempty (PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments) := by sorry
