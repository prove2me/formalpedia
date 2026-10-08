-- Prove2me | Theorems.Thm_PlaneDrawingDartArcEndpointAwaySeparation
-- name    : PlaneDrawingDartArcEndpointAwaySeparation
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T21:04:39.340804+00:00
-- url     : https://prove2.me/theorems/7010f6b0-6d8d-4920-8ccf-66bb51121c21
-- title:
--   Plane Drawing Dart Arc Endpoint Away Separation
-- statement:
--   Let $D$ be a crossing-free ordinary polygonal drawing, let $A$ be
--   dart-arc data, let $d$ be a dart, and let $r_0,r_1>0$.  Then there is a
--   positive number $\delta$ such that every point of
--   $$
--     \mathsf{OrdinaryDrawingImageWithoutEdge}(G,D,A.dartEdge(d))
--       \setminus\bigl(B((A.dartArc(d)).source,r_0)\cup
--         B((A.dartArc(d)).target,r_1)\bigr)
--   $$
--   has distance at least $\delta$ from every point of the carrier of
--   $A.dartArc(d)$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PlaneDrawingDartArcEndpointAwaySeparation`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneDrawingDartArcEndpointAwaySeparation.lean#L1-L97

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Topology.Order.Compact
import Definitions.Def_OrdinaryDrawingImageWithoutEdge
import Definitions.Def_OrdinaryPolygonalDrawing
import Definitions.Def_PlaneDrawingDartArcData

open Classical
noncomputable section

lemma PlaneDrawingDartArcEndpointAwaySeparation {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (A : PlaneDrawingDartArcData G D) (d : G.Dart) (r₀ r₁ : ℝ) :
    0 < r₀ →
      0 < r₁ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ x : EuclideanSpace ℝ (Fin 2),
            x ∈ OrdinaryDrawingImageWithoutEdge G D (A.dartEdge d) →
              x ∉ Metric.ball (A.dartArc d).source r₀ ∪
                Metric.ball (A.dartArc d).target r₁ →
                ∀ p : EuclideanSpace ℝ (Fin 2),
                  p ∈ (A.dartArc d).carrier →
                    δ ≤ dist x p := by sorry
