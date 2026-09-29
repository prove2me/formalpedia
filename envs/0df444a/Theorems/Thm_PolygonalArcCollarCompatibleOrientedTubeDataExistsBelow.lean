-- Prove2me | Theorems.Thm_PolygonalArcCollarCompatibleOrientedTubeDataExistsBelow
-- name    : PolygonalArcCollarCompatibleOrientedTubeDataExistsBelow
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T23:54:46.485997+00:00
-- url     : https://prove2.me/theorems/cae35add-c01d-45ba-8839-d5ec34641fc3
-- title:
--   PolygonalArcCollarCompatibleOrientedTubeDataExistsBelow
-- statement:
--   Given a polygonal arc, collar-control radii, middle segments, forbidden margins, endpoint-isolation radii, and positive cone bounds, there exist compatible oriented tube data whose endpoint cone bounds fit the prescribed constants and whose non-endpoint tubes avoid the endpoint balls.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarCompatibleOrientedTubeDataExistsBelow.lean#L1-51

import Definitions.Def_PolygonalArcCollarCompatibleOrientedTubeData
import Definitions.Def_PolygonalArcEndpointIsolation

import Mathlib.Tactic

open Classical
noncomputable section

lemma PolygonalArcCollarCompatibleOrientedTubeDataExistsBelow (γ : PolygonalArc)
    {η : ℝ} (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (r₀ r₁ K₀ K₁ : ℝ) :
    PolygonalArcEndpointIsolation γ r₀ r₁ →
      0 < K₀ →
      0 < K₁ →
        let hfirst : 0 + 1 < γ.vertices.length := by
          have hlen := γ.length_ge_two
          omega
        let jlast : ℕ := γ.vertices.length - 2
        let hlast : jlast + 1 < γ.vertices.length := by
          have hlen := γ.length_ge_two
          dsimp [jlast]
          omega
        ∃ compatibleTubes :
          PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii
            middleSegments forbiddenMargins,
          compatibleTubes.initialConeBound 0 hfirst < K₀ ∧
            compatibleTubes.terminalConeBound jlast hlast < K₁ ∧
              (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), j ≠ 0 →
                Disjoint
                  (compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.tube
                    j hj)
                  (Metric.ball γ.source r₀)) ∧
                (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), j ≠ jlast →
                  Disjoint
                    (compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.tube
                      j hj)
                    (Metric.ball γ.target r₁)) := by sorry
