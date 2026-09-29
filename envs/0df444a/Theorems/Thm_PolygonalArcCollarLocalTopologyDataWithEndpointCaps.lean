-- Prove2me | Theorems.Thm_PolygonalArcCollarLocalTopologyDataWithEndpointCaps
-- name    : PolygonalArcCollarLocalTopologyDataWithEndpointCaps
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-28T03:51:58.302824+00:00
-- url     : https://prove2.me/theorems/da51b4b8-fffb-4457-abe7-1fae7c7c6da5
-- title:
--   Endpoint-capped local topology for a polygonal-arc collar
-- statement:
--   For fixed control radii, middle-segment data, forbidden margins, and compatible oriented tubes on a polygonal arc, assume positive endpoint radii and positive endpoint cone bounds. If the endpoint vertex radii and the initial and terminal cone bounds are strictly below those prescribed quantities, there exist vertex-local pieces and a local-topology datum with endpoint collars that avoid the source and target, lie in the corresponding endpoint cones away from the arc, and have left/right side pieces in the stated forward and reversed endpoint left cones. The datum additionally admits exact endpoint chart descriptions: the source collar is a capped two-sided wedge, while the target collar has the analogous chart with the terminal left/right labels swapped.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarLocalTopologyDataWithEndpointCaps.lean#L1-130

import Mathlib.Tactic
import Definitions.Def_PolygonalArcCollarLocalTopologyData
import Definitions.Def_PolygonalArcInitialEndpointCone
import Definitions.Def_PolygonalArcInitialEndpointLeftCone
import Definitions.Def_PolygonalArcReverse
import Definitions.Def_PolygonalArcTerminalEndpointCone
import Definitions.Def_PolygonalArcTerminalEndpointLeftCone

open Set
open Classical
noncomputable section

set_option maxHeartbeats 2200000

lemma PolygonalArcCollarLocalTopologyDataWithEndpointCaps (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
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
              exact Nat.lt_trans Nat.zero_lt_one γ.length_ge_two
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
                    ∃ vertexLocalPieces :
                        PolygonalArcCollarVertexLocalPieceData γ controlRadii
                          middleSegments forbiddenMargins
                          compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData,
                      ∃ localTopology :
                        PolygonalArcCollarLocalTopologyData γ controlRadii
                          middleSegments forbiddenMargins compatibleTubes
                          vertexLocalPieces,
                        γ.source ∉ localTopology.vertexCollar ⟨0, hsource⟩ ∧
                          γ.target ∉ localTopology.vertexCollar ⟨itarget, htarget⟩ ∧
                            (localTopology.vertexCollar ⟨0, hsource⟩ \
                                γ.relativeInterior ⊆
                              PolygonalArcInitialEndpointCone γ r₀ K₀) ∧
                              (localTopology.vertexCollar ⟨itarget, htarget⟩ \
                                  γ.relativeInterior ⊆
                                PolygonalArcTerminalEndpointCone γ r₁ K₁) ∧
                                localTopology.leftSidePiece ⟨0, hsource⟩ ⊆
                                  PolygonalArcInitialEndpointLeftCone γ r₀ K₀ ∧
                                  localTopology.leftSidePiece ⟨itarget, htarget⟩ ⊆
                                    PolygonalArcTerminalEndpointLeftCone γ r₁ K₁ ∧
                                    localTopology.rightSidePiece ⟨0, hsource⟩ ⊆
                                      PolygonalArcTerminalEndpointLeftCone
                                        (PolygonalArcReverse γ) r₀ K₀ ∧
                                      localTopology.rightSidePiece
                                          ⟨itarget, htarget⟩ ⊆
                                        PolygonalArcInitialEndpointLeftCone
                                          (PolygonalArcReverse γ) r₁ K₁ ∧
                                        (let E := EuclideanSpace ℝ (Fin 2)
                                         let d0 : E := γ.vertices[1] - γ.vertices[0]
                                         let chart0 : E → E := fun z =>
                                           γ.vertices[0] + z 0 • d0 +
                                             z 1 • PlanarRot90 d0
                                         let a0 : ℝ :=
                                           controlRadii.radius ⟨0, hsource⟩ /
                                             dist γ.vertices[0] γ.vertices[1]
                                         let κ0 : ℝ :=
                                           compatibleTubes.initialConeBound 0 hfirst
                                         let C0 : Set E :=
                                           {z | 0 < z 0 ∧
                                             z 0 ^ 2 + z 1 ^ 2 < a0 ^ 2 ∧
                                             -κ0 * z 0 < z 1 ∧ z 1 < κ0 * z 0}
                                         let L0 : Set E :=
                                           {z | 0 < z 0 ∧
                                             z 0 ^ 2 + z 1 ^ 2 < a0 ^ 2 ∧
                                             0 < z 1 ∧ z 1 < κ0 * z 0}
                                         let R0 : Set E :=
                                           {z | 0 < z 0 ∧
                                             z 0 ^ 2 + z 1 ^ 2 < a0 ^ 2 ∧
                                             -κ0 * z 0 < z 1 ∧ z 1 < 0}
                                         let dT : E :=
                                           γ.vertices[jlast] - γ.vertices[itarget]
                                         let chartT : E → E := fun z =>
                                           γ.vertices[itarget] + z 0 • dT +
                                             z 1 • PlanarRot90 dT
                                         let aT : ℝ :=
                                           controlRadii.radius ⟨itarget, htarget⟩ /
                                             dist γ.vertices[itarget] γ.vertices[jlast]
                                         let κT : ℝ :=
                                           compatibleTubes.terminalConeBound jlast hlast
                                         let CT : Set E :=
                                           {z | 0 < z 0 ∧
                                             z 0 ^ 2 + z 1 ^ 2 < aT ^ 2 ∧
                                             -κT * z 0 < z 1 ∧ z 1 < κT * z 0}
                                         let LT : Set E :=
                                           {z | 0 < z 0 ∧
                                             z 0 ^ 2 + z 1 ^ 2 < aT ^ 2 ∧
                                             0 < z 1 ∧ z 1 < κT * z 0}
                                         let RT : Set E :=
                                           {z | 0 < z 0 ∧
                                             z 0 ^ 2 + z 1 ^ 2 < aT ^ 2 ∧
                                             -κT * z 0 < z 1 ∧ z 1 < 0}
                                         localTopology.vertexCollar ⟨0, hsource⟩ =
                                             chart0 '' C0 ∧
                                           localTopology.leftSidePiece ⟨0, hsource⟩ =
                                             chart0 '' L0 ∧
                                           localTopology.rightSidePiece ⟨0, hsource⟩ =
                                             chart0 '' R0 ∧
                                           localTopology.vertexCollar
                                               ⟨itarget, htarget⟩ = chartT '' CT ∧
                                           localTopology.leftSidePiece
                                               ⟨itarget, htarget⟩ = chartT '' RT ∧
                                           localTopology.rightSidePiece
                                               ⟨itarget, htarget⟩ = chartT '' LT) := by sorry
