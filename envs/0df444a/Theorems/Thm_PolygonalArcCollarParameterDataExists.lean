-- Prove2me | Theorems.Thm_PolygonalArcCollarParameterDataExists
-- name    : PolygonalArcCollarParameterDataExists
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-28T02:01:26.416985+00:00
-- url     : https://prove2.me/theorems/aa0f46a4-139e-4115-b88c-cc98c5bbae34
-- title:
--   Existence of polygonal arc collar parameter data
-- statement:
--   For a polygonal arc with fixed control radii, middle segments, and forbidden margins, there exists a coherent parameter package for every segment. It supplies the left and right normalized parameters, a segment-length scale, a positive slack, lower and upper tube parameters, and the positively oriented normal.
--
--   The package includes the exact identities with the control-radius formulas and the inequalities needed to place the interval strictly inside the segment parameter range, together with the orthogonality and norm relations for the normal. It is the parameter-phase interface used by the subsequent compact-separation and tube-construction phases.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarCompatibleOrientedTubeDataExists.lean#L109-L332

import Definitions.Def_PolygonalArcCollarParameterData
import Theorems.Thm_PlanarRot90Norm
import Theorems.Thm_PlanarRot90Orthogonal

open Classical
noncomputable section

theorem PolygonalArcCollarParameterDataExists (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments) :
    Nonempty
      (PolygonalArcCollarParameterData γ controlRadii middleSegments forbiddenMargins) := by sorry
