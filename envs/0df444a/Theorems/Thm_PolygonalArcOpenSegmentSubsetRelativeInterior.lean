-- Prove2me | Theorems.Thm_PolygonalArcOpenSegmentSubsetRelativeInterior
-- name    : PolygonalArcOpenSegmentSubsetRelativeInterior
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T21:59:47.644739+00:00
-- url     : https://prove2.me/theorems/d39953de-2383-4411-ae0f-d348ff3156dc
-- title:
--   Open polygonal-arc segments lie in the relative interior
-- statement:
--   Let γ be a polygonal arc and let j index one of its consecutive edges. Every point of the open segment between γ.vertices[j] and γ.vertices[j+1] belongs to γ's relative interior. The endpoint exclusions follow from the arc's simple-vertex and nonincident-interior conditions, so an open edge contributes no endpoint to the relative boundary.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcOpenSegmentSubsetRelativeInterior.lean#L1-74

import Definitions.Def_PolygonalArc

open Classical
noncomputable section

lemma PolygonalArcOpenSegmentSubsetRelativeInterior (γ : PolygonalArc) (j : ℕ)
    (hj : j + 1 < γ.vertices.length) :
    openSegment ℝ γ.vertices[j] γ.vertices[j + 1] ⊆ γ.relativeInterior := by sorry
