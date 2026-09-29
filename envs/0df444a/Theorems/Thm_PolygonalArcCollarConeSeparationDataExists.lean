-- Prove2me | Theorems.Thm_PolygonalArcCollarConeSeparationDataExists
-- name    : PolygonalArcCollarConeSeparationDataExists
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-28T02:12:36.963295+00:00
-- url     : https://prove2.me/theorems/30b70438-8b5c-474e-a0e6-542ffc9a3bfe
-- title:
--   Existence of cone bounds and signed-cone separation data
-- statement:
--   For the fixed polygonal arc collar inputs, there exist positive initial and terminal cone bounds. With the positive quarter-turn of each segment direction as the normal, the corresponding initial, terminal, and two successive signed cones are disjoint from the required neighboring segment or cone.
--
--   This is the independent cone-algebra phase of the compatible oriented tube construction. Its conclusions use the explicit quarter-turn expressions so that the final assembly can identify them with the normal field of the oriented tube.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarCompatibleOrientedTubeDataExists.lean#L29-L109, L1190-L1461

import Definitions.Def_PolygonalArcCollarConeSeparationData
import Theorems.Thm_PolygonalArcAdjacentOutwardDirectionsNotSameRay
import Theorems.Thm_PlanarRot90ConeAvoidsRay

open Classical
noncomputable section

-- cone-bound and signed-cone separation phase.

theorem PolygonalArcCollarConeSeparationDataExists (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments) :
    Nonempty
      (PolygonalArcCollarConeSeparationData γ controlRadii middleSegments
        forbiddenMargins) := by sorry
