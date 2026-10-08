-- Prove2me | Theorems.Thm_PolygonalArcEndpointLeftHalfTubeSubsetLeftCones
-- name    : PolygonalArcEndpointLeftHalfTubeSubsetLeftCones
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T21:04:44.388573+00:00
-- url     : https://prove2.me/theorems/7a28574c-54b7-47ad-998e-6c983c7d3a3b
-- title:
--   Polygonal Arc Endpoint Left Half Tube Subset Left Cones
-- statement:
--   Let $\gamma$ be a polygonal arc with fixed collar control radii, middle
--   segments, forbidden margins, and compatible oriented tube data.  Let
--   $r_0,r_1$ be endpoint-isolating radii for $\gamma$, and let
--   $K_0,K_1>0$.  If the compatible tube datum has initial cone bound on the
--   first segment smaller than $K_0$, and terminal cone bound on the last
--   segment smaller than $K_1$, then
--   $$
--     T^+_0\cap B(\gamma.source,r_0)
--       \subseteq PolygonalArcInitialEndpointLeftCone(\gamma,r_0,K_0)
--   $$
--   and
--   $$
--     T^+_{last}\cap B(\gamma.target,r_1)
--       \subseteq PolygonalArcTerminalEndpointLeftCone(\gamma,r_1,K_1),
--   $$
--   where $T^+_0$ and $T^+_{last}$ are the left half-tubes of the first and
--   last listed segments.  In addition, the right half-tubes satisfy the
--   reverse-orientation endpoint containments
--   $$
--     T^-_0\cap B(\gamma.source,r_0)
--       \subseteq
--     PolygonalArcTerminalEndpointLeftCone
--       (PolygonalArcReverse(\gamma),r_0,K_0)
--   $$
--   and
--   $$
--     T^-_{last}\cap B(\gamma.target,r_1)
--       \subseteq
--     PolygonalArcInitialEndpointLeftCone
--       (PolygonalArcReverse(\gamma),r_1,K_1).
--   $$
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PolygonalArcEndpointLeftHalfTubeSubsetLeftCones`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcEndpointLeftHalfTubeSubsetLeftCones.lean#L1-L479

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Definitions.Def_PolygonalArc
import Definitions.Def_PolygonalArcCollarCompatibleOrientedTubeData
import Definitions.Def_PolygonalArcCollarControlRadii
import Definitions.Def_PolygonalArcCollarMiddleForbiddenMargins
import Definitions.Def_PolygonalArcCollarMiddleSegmentData
import Definitions.Def_PolygonalArcEndpointIsolation
import Definitions.Def_PolygonalArcInitialEndpointLeftCone
import Definitions.Def_PolygonalArcReverse
import Definitions.Def_PolygonalArcTerminalEndpointLeftCone

open Classical
noncomputable section

lemma PolygonalArcEndpointLeftHalfTubeSubsetLeftCones (γ : PolygonalArc)
    {η : ℝ} (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (compatibleTubes :
      PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (r₀ r₁ K₀ K₁ : ℝ) :
    PolygonalArcEndpointIsolation γ r₀ r₁ →
      0 < K₀ →
        0 < K₁ →
          ∀ (hfirst : 0 + 1 < γ.vertices.length)
            (hlast : (γ.vertices.length - 2) + 1 < γ.vertices.length),
            compatibleTubes.initialConeBound 0 hfirst < K₀ →
              compatibleTubes.terminalConeBound (γ.vertices.length - 2) hlast <
                K₁ →
                (compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf
                    0 hfirst ∩ Metric.ball γ.source r₀ ⊆
                  PolygonalArcInitialEndpointLeftCone γ r₀ K₀) ∧
                  (compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf
                      (γ.vertices.length - 2) hlast ∩
                        Metric.ball γ.target r₁ ⊆
                    PolygonalArcTerminalEndpointLeftCone γ r₁ K₁) ∧
                    (compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf
                        0 hfirst ∩ Metric.ball γ.source r₀ ⊆
                      PolygonalArcTerminalEndpointLeftCone
                        (PolygonalArcReverse γ) r₀ K₀) ∧
                      (compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf
                          (γ.vertices.length - 2) hlast ∩
                            Metric.ball γ.target r₁ ⊆
                        PolygonalArcInitialEndpointLeftCone
                          (PolygonalArcReverse γ) r₁ K₁) := by sorry
