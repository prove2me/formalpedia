-- Prove2me | Theorems.Thm_PolygonalArcCollarOrientedTubeWitnessExists
-- name    : PolygonalArcCollarOrientedTubeWitnessExists
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-28T02:04:36.714184+00:00
-- url     : https://prove2.me/theorems/98b48977-c817-4c9f-bdfb-7ba434e59e92
-- title:
--   Existence of an oriented separated tube witness
-- statement:
--   Given parameter data, centerline separation data, and positive initial and terminal cone bounds, there exists an oriented separated tube package. Its half-width construction satisfies the two cone-width inequalities and all three required width-versus-away-separation inequalities; the underlying oriented tube also carries the eta, margin, normal, and disjointness fields of the separated-tube definition.
--
--   The cone bounds are explicit inputs rather than consequences of this theorem. This makes the half-width and tube phase independent from the separate signed-cone geometry phase, while retaining the exact dependencies of the original construction.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarCompatibleOrientedTubeDataExists.lean#L614-L1174

import Definitions.Def_PolygonalArcCollarOrientedTubeWitness
import Theorems.Thm_PlanarRot90Norm
import Theorems.Thm_PlanarRot90Orthogonal

open Classical
noncomputable section

-- half-width/tube construction and disjointness phase.

theorem PolygonalArcCollarOrientedTubeWitnessExists (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (parameters :
      PolygonalArcCollarParameterData γ controlRadii middleSegments forbiddenMargins)
    (separations :
      PolygonalArcCollarCenterlineSeparationData γ controlRadii middleSegments
        forbiddenMargins parameters)
    (initialConeBound terminalConeBound :
      (j : ℕ) → j + 1 < γ.vertices.length → ℝ)
    (initialConeBound_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < initialConeBound j hj)
    (terminalConeBound_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < terminalConeBound j hj) :
    Nonempty
      (PolygonalArcCollarOrientedTubeWitness γ controlRadii middleSegments
        forbiddenMargins parameters separations initialConeBound terminalConeBound
        initialConeBound_pos terminalConeBound_pos) := by sorry
