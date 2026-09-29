-- Prove2me | Theorems.Thm_PolygonalArcCollarLocalSideDataExistsWithEndpointLeftCones
-- name    : PolygonalArcCollarLocalSideDataExistsWithEndpointLeftCones
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-27T23:55:31.109984+00:00
-- url     : https://prove2.me/theorems/7797956b-a1a4-4d17-b9ee-3ad0681534f8
-- title:
--   PolygonalArcCollarLocalSideDataExistsWithEndpointLeftCones
-- statement:
--   Under the quantitative endpoint and tube compatibility hypotheses for a polygonal-arc collar, there exist vertex-local pieces and local side data whose endpoint collars and left/right side pieces satisfy the stated cone containment, disjointness, and endpoint-ball avoidance conditions.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarLocalSideDataExistsWithEndpointLeftCones.lean#L1-130

import Definitions.Def_PolygonalArcCollarLocalSideData
import Definitions.Def_PolygonalArcCollarCompatibleOrientedTubeData
import Definitions.Def_PolygonalArcInitialEndpointCone
import Definitions.Def_PolygonalArcInitialEndpointLeftCone
import Definitions.Def_PolygonalArcReverse
import Definitions.Def_PolygonalArcTerminalEndpointCone
import Definitions.Def_PolygonalArcTerminalEndpointLeftCone

import Mathlib.Tactic

open Classical
noncomputable section

lemma PolygonalArcCollarLocalSideDataExistsWithEndpointLeftCones (γ : PolygonalArc)
    {η : ℝ} (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (compatibleTubes :
      PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (r₀ r₁ K₀ K₁ : ℝ) :
    0 < r₀ →
      0 < r₁ →
        0 < K₀ →
          0 < K₁ →
            let hsource : 0 < γ.vertices.length := by
              have hlen := γ.length_ge_two
              omega
            let hfirst : 0 + 1 < γ.vertices.length := by
              have hlen := γ.length_ge_two
              omega
            let itarget : ℕ := γ.vertices.length - 1
            let htarget : itarget < γ.vertices.length := by
              have hlen := γ.length_ge_two
              dsimp [itarget]
              omega
            let jlast : ℕ := γ.vertices.length - 2
            let hlast : jlast + 1 < γ.vertices.length := by
              have hlen := γ.length_ge_two
              dsimp [jlast]
              omega
            controlRadii.radius ⟨0, hsource⟩ < r₀ →
              controlRadii.radius ⟨itarget, htarget⟩ < r₁ →
                compatibleTubes.initialConeBound 0 hfirst < K₀ →
                  compatibleTubes.terminalConeBound jlast hlast < K₁ →
                    (∀ i : Fin γ.vertices.length, i.1 ≠ 0 →
                      Disjoint
                        (Metric.ball γ.vertices[i.1] (controlRadii.radius i))
                        (Metric.ball γ.source r₀)) →
                      (∀ i : Fin γ.vertices.length,
                        i.1 + 1 ≠ γ.vertices.length →
                          Disjoint
                            (Metric.ball γ.vertices[i.1] (controlRadii.radius i))
                            (Metric.ball γ.target r₁)) →
                        ∃ vertexLocalPieces :
                            PolygonalArcCollarVertexLocalPieceData γ controlRadii
                              middleSegments forbiddenMargins
                              compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData,
                          ∃ localSideData :
                            PolygonalArcCollarLocalSideData γ controlRadii
                              middleSegments forbiddenMargins compatibleTubes.orientedTubes
                              vertexLocalPieces,
                            γ.source ∉ localSideData.vertexCollar ⟨0, hsource⟩ ∧
                              γ.target ∉ localSideData.vertexCollar ⟨itarget, htarget⟩ ∧
                                (localSideData.vertexCollar ⟨0, hsource⟩ \
                                    γ.relativeInterior ⊆
                                  PolygonalArcInitialEndpointCone γ r₀ K₀) ∧
                                  (localSideData.vertexCollar ⟨itarget, htarget⟩ \
                                      γ.relativeInterior ⊆
                                    PolygonalArcTerminalEndpointCone γ r₁ K₁) ∧
                                    (∀ i : Fin γ.vertices.length, i.1 ≠ 0 →
                                      Disjoint (localSideData.vertexCollar i)
                                        (Metric.ball γ.source r₀)) ∧
                                      (∀ i : Fin γ.vertices.length,
                                        i.1 + 1 ≠ γ.vertices.length →
                                          Disjoint (localSideData.vertexCollar i)
                                            (Metric.ball γ.target r₁)) ∧
                                        localSideData.leftSidePiece ⟨0, hsource⟩ ⊆
                                          PolygonalArcInitialEndpointLeftCone γ r₀ K₀ ∧
                                          localSideData.leftSidePiece
                                              ⟨itarget, htarget⟩ ⊆
                                            PolygonalArcTerminalEndpointLeftCone γ r₁ K₁ ∧
                                            localSideData.rightSidePiece
                                                ⟨0, hsource⟩ ⊆
                                              PolygonalArcTerminalEndpointLeftCone
                                                (PolygonalArcReverse γ) r₀ K₀ ∧
                                              localSideData.rightSidePiece
                                                  ⟨itarget, htarget⟩ ⊆
                                                PolygonalArcInitialEndpointLeftCone
                                                  (PolygonalArcReverse γ) r₁ K₁ := by sorry
