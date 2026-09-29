-- Prove2me | Theorems.Thm_PolygonalArcCollarCompatibleOrientedTubeDataEndpointRefinement
-- name    : PolygonalArcCollarCompatibleOrientedTubeDataEndpointRefinement
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-28T00:31:26.632386+00:00
-- url     : https://prove2.me/theorems/ea3bf379-b13a-4bdc-9b86-761cf1a65bc6
-- title:
--   Endpoint refinement for compatible oriented tube data
-- statement:
--   Fix a polygonal arc together with its control radii, middle segments, forbidden margins, and an already compatible oriented tube datum. If r₀ and r₁ give endpoint isolation and K₀,K₁ are positive, then one can refine the tube datum so that the initial cone bound on the first segment is below K₀, the terminal cone bound on the last segment is below K₁, every non-first tube avoids the source ball of radius r₀, and every non-last tube avoids the target ball of radius r₁.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarCompatibleOrientedTubeDataEndpointRefinement.lean#L1-L46

import Definitions.Def_PolygonalArcCollarCompatibleOrientedTubeData
import Definitions.Def_PolygonalArcEndpointIsolation

import Mathlib.Tactic

open Classical
noncomputable section

lemma PolygonalArcCollarCompatibleOrientedTubeDataEndpointRefinement (γ : PolygonalArc)
    {η : ℝ} (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (base :
      PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (r₀ r₁ K₀ K₁ : ℝ) :
    PolygonalArcEndpointIsolation γ r₀ r₁ →
      0 < K₀ →
      0 < K₁ →
        let hfirst : 0 + 1 < γ.vertices.length := by
          have hlen := γ.length_ge_two
          omega
        let jlast : ℕ := γ.vertices.length - 2
        let hlast : jlast + 1 < γ.vertices.length := by
          have _hlen := γ.length_ge_two
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
