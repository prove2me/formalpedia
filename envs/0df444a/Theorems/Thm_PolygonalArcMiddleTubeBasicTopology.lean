-- Prove2me | Theorems.Thm_PolygonalArcMiddleTubeBasicTopology
-- name    : PolygonalArcMiddleTubeBasicTopology
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-28T05:03:23.12354+00:00
-- url     : https://prove2.me/theorems/2b0eeb74-ced2-472d-8adb-eae099f16898
-- title:
--   Basic topology of polygonal-arc middle tubes
-- statement:
--   For every middle segment of a polygonal arc, the associated separated tube and its two oriented half-tubes are open, and each half-tube is connected. This is the local topological input used when assembling the global left and right side strips.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcMiddleTubeBasicTopology.lean#L1-L27

import Definitions.Def_PolygonalArcCollarOrientedSeparatedTubeData
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension

open Classical
noncomputable section

lemma PolygonalArcMiddleTubeBasicTopology
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (orientedTubes :
      PolygonalArcCollarOrientedSeparatedTubeData γ controlRadii middleSegments
        forbiddenMargins) :
    (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      IsOpen (orientedTubes.toPolygonalArcCollarSeparatedTubeData.tube j hj)) ∧
    (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      IsOpen (orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf j hj)) ∧
    (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      IsOpen (orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf j hj)) ∧
    (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      IsConnected (orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf j hj)) ∧
    (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      IsConnected (orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf j hj)) := by sorry
