-- Prove2me | Theorems.Thm_PolygonalArcCollarCenterlineSeparationDataExists
-- name    : PolygonalArcCollarCenterlineSeparationDataExists
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-28T02:03:25.975843+00:00
-- url     : https://prove2.me/theorems/47ff0718-5c7b-41ea-985b-0272fefc0d32
-- title:
--   Existence of compact centerline separation data
-- statement:
--   Given the parameter package for a polygonal arc collar, there exist positive initial, terminal, and successive separation functions. They bound the distance between the trimmed centerline portions and their neighboring segments or centerline portions.
--
--   The conclusion preserves the original control-radius parameter intervals exactly. This is the compactness and positive-separation interface used to choose a tube width that remains away from all nonincident geometric pieces.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarCompatibleOrientedTubeDataExists.lean#L332-L614

import Definitions.Def_PolygonalArcCollarCenterlineSeparationData
import Theorems.Thm_PositiveSeparation

open Classical
noncomputable section

-- compact centerline/PositiveSeparation phase.

theorem PolygonalArcCollarCenterlineSeparationDataExists (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (parameters :
      PolygonalArcCollarParameterData γ controlRadii middleSegments forbiddenMargins) :
    Nonempty
      (PolygonalArcCollarCenterlineSeparationData γ controlRadii middleSegments
        forbiddenMargins parameters) := by sorry
