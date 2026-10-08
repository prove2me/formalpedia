-- Prove2me | Theorems.Thm_PlaneDrawingDartUnitFirstGermsForRadii
-- name    : PlaneDrawingDartUnitFirstGermsForRadii
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T21:05:28.297887+00:00
-- url     : https://prove2.me/theorems/9a9a9c5a-d50d-48ce-be17-bee98513b229
-- title:
--   Plane Drawing Dart Unit First Germs For Radii
-- statement:
--   Let $G$ be a finite simple graph, let $D$ be an ordinary polygonal drawing
--   of $G$, and let $A$ be dart-arc data.  Let $R_v>0$ be a positive radius at
--   each vertex, and suppose that for every outgoing dart $d$ with tail $v$, the
--   radius $R_v$ is at most the length of the first segment vector of
--   $A.dartArc(d)$ at $D(v)$.  Then there are nonzero germ directions and radial
--   germs for all outgoing darts such that, for each outgoing dart $d$ at $v$,
--   the germ direction is the normalized first segment vector
--   $$
--     u_{v,d}=\|q_{v,d}\|^{-1}q_{v,d},
--     \qquad q_{v,d}=(A.dartArc(d)).vertices_1-D(v),
--   $$
--   and each radial germ has the form
--   $$
--     \operatorname{openSegment}(D(v),D(v)+r_{v,d}u_{v,d})
--   $$
--   for its chosen germ direction $u_{v,d}$ and some $0<r_{v,d}\le R_v$.
--   Moreover, in this construction the same radial germ is exactly the
--   full-radius segment
--   $$
--     \operatorname{openSegment}(D(v),D(v)+R_v u_{v,d}).
--   $$
--   It is contained in the corresponding drawn edge carrier and in the metric ball
--   $B(D(v),R_v)$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PlaneDrawingDartUnitFirstGermsForRadii`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneDrawingDartUnitFirstGermsForRadii.lean#L1-L199

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Definitions.Def_OrdinaryPolygonalDrawing
import Definitions.Def_PlaneDrawingDartArcData

open Classical
noncomputable section

lemma PlaneDrawingDartUnitFirstGermsForRadii {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G)
    (A : PlaneDrawingDartArcData G D)
    (R : V → ℝ) (hR : ∀ v : V, 0 < R v)
    (hR_le_first :
      ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
        R v ≤ ‖(A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le (A.dartArc d.1).length_ge_two) -
          D.vertexPlacement v‖) :
    ∃ germDirection :
        ∀ v : V, {d : G.Dart // d.toProd.1 = v} → EuclideanSpace ℝ (Fin 2),
      ∃ radialGerm :
        ∀ v : V, {d : G.Dart // d.toProd.1 = v} →
          Set (EuclideanSpace ℝ (Fin 2)),
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          germDirection v d ≠ 0) ∧
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          germDirection v d =
            (‖(A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le
                  (A.dartArc d.1).length_ge_two) - D.vertexPlacement v‖)⁻¹ •
              ((A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le
                  (A.dartArc d.1).length_ge_two) - D.vertexPlacement v)) ∧
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          ∃ r : ℝ, 0 < r ∧ r ≤ R v ∧
            radialGerm v d =
              openSegment ℝ (D.vertexPlacement v)
                (D.vertexPlacement v + r • germDirection v d)) ∧
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          radialGerm v d =
            openSegment ℝ (D.vertexPlacement v)
              (D.vertexPlacement v + R v • germDirection v d)) ∧
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          radialGerm v d ⊆ (D.edgeArc (A.dartEdge d.1)).carrier) ∧
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          radialGerm v d ⊆ Metric.ball (D.vertexPlacement v) (R v)) := by sorry
