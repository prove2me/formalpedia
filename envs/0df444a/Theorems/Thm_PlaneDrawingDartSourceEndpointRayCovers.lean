-- Prove2me | Theorems.Thm_PlaneDrawingDartSourceEndpointRayCovers
-- name    : PlaneDrawingDartSourceEndpointRayCovers
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T21:05:16.878083+00:00
-- url     : https://prove2.me/theorems/e9173032-cf22-4dd8-bf69-ffd627b42ad9
-- title:
--   Plane Drawing Dart Source Endpoint Ray Covers
-- statement:
--   Let $G$ be a finite simple graph, let $D$ be an ordinary polygonal drawing
--   of $G$, and let $A$ be dart-arc data
--   `PlaneDrawingDartArcData`.  For every outgoing dart $d$ at a
--   vertex $v$, there is a positive radius around $D(v)$ on which the carrier
--   of the corresponding drawn edge lies on the source ray determined by the first
--   segment of the dart arc $A.dartArc(d)$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PlaneDrawingDartSourceEndpointRayCovers`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneDrawingDartSourceEndpointRayCovers.lean#L1-L54

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_OrdinaryPolygonalDrawing
import Definitions.Def_PlaneDrawingDartArcData

open Classical
noncomputable section

lemma PlaneDrawingDartSourceEndpointRayCovers {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G)
    (A : PlaneDrawingDartArcData G D) :
    ∃ sourceRayRadius :
        ∀ v : V, {d : G.Dart // d.toProd.1 = v} → ℝ,
      (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
        0 < sourceRayRadius v d) ∧
      ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
        let γ := A.dartArc d.1
        let hfirst : 1 < γ.vertices.length :=
          Nat.lt_of_succ_le γ.length_ge_two
        Metric.ball (D.vertexPlacement v) (sourceRayRadius v d) ∩
            (D.edgeArc (A.dartEdge d.1)).carrier ⊆
          {x | ∃ c : ℝ, 0 ≤ c ∧
            x = D.vertexPlacement v +
              c • (γ.vertices[1]'hfirst - D.vertexPlacement v)} := by sorry
