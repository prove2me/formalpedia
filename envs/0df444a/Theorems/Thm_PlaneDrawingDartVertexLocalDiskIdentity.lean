-- Prove2me | Theorems.Thm_PlaneDrawingDartVertexLocalDiskIdentity
-- name    : PlaneDrawingDartVertexLocalDiskIdentity
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T21:05:34.269893+00:00
-- url     : https://prove2.me/theorems/399a43eb-332b-43af-a119-bce95bb18e29
-- title:
--   Plane Drawing Dart Vertex Local Disk Identity
-- statement:
--   Let $G$ be a finite simple graph, let $D$ be a crossing-free ordinary
--   polygonal drawing of $G$, and let $A$ be dart-arc data for $D$.
--   Then one can choose, for every vertex $v$, a radius $\rho_v>0$, and,
--   for every outgoing dart $a$ with tail $v$, a unit first-germ direction
--   $$
--     u_{v,a}
--     =
--     \left\|(A.dartArc(a)).vertices_1-D(v)\right\|^{-1}
--     \bigl((A.dartArc(a)).vertices_1-D(v)\bigr)
--   $$
--   and a radial germ
--   $$
--     R_{v,a}
--     =
--     \operatorname{openSegment}\bigl(D(v),D(v)+\rho_v u_{v,a}\bigr),
--   $$
--   such that $R_{v,a}$ is contained in the carrier of the edge of $a$ and
--   $$
--     B(D(v),\rho_v)\cap |D|
--     =
--     \{D(v)\}\cup\bigcup_{\operatorname{tail}(a)=v}R_{v,a}.
--   $$
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PlaneDrawingDartVertexLocalDiskIdentity`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneDrawingDartVertexLocalDiskIdentity.lean#L1-L442

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
import Definitions.Def_PlaneFaceData

open Classical
noncomputable section

lemma PlaneDrawingDartVertexLocalDiskIdentity {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (A : PlaneDrawingDartArcData G D) :
    ∃ localDiskRadius : V → ℝ,
      ∃ germDirection :
        ∀ v : V, {d : G.Dart // d.toProd.1 = v} → EuclideanSpace ℝ (Fin 2),
      ∃ radialGerm :
        ∀ v : V, {d : G.Dart // d.toProd.1 = v} →
          Set (EuclideanSpace ℝ (Fin 2)),
        (∀ v : V, 0 < localDiskRadius v) ∧
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          germDirection v d ≠ 0) ∧
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          germDirection v d =
            (‖(A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le
                  (A.dartArc d.1).length_ge_two) - D.vertexPlacement v‖)⁻¹ •
              ((A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le
                  (A.dartArc d.1).length_ge_two) - D.vertexPlacement v)) ∧
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          radialGerm v d =
            openSegment ℝ (D.vertexPlacement v)
              (D.vertexPlacement v + localDiskRadius v • germDirection v d)) ∧
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          radialGerm v d ⊆ (D.edgeArc (A.dartEdge d.1)).carrier) ∧
        (∀ v : V,
          Metric.ball (D.vertexPlacement v) (localDiskRadius v) ∩
              OrdinaryDrawingImage G D =
            {D.vertexPlacement v} ∪
              ⋃ d : {d : G.Dart // d.toProd.1 = v}, radialGerm v d) := by sorry
