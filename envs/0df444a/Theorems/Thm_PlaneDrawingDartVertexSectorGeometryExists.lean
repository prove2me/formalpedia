-- Prove2me | Theorems.Thm_PlaneDrawingDartVertexSectorGeometryExists
-- name    : PlaneDrawingDartVertexSectorGeometryExists
-- status  : Open
-- author  : @moona3k
-- created : 2026-10-04T21:40:57.678039+00:00
-- url     : https://prove2.me/theorems/fb712040-6a8f-4d5b-a8f2-548b888ebfc9
-- title:
--   Plane Drawing Dart Vertex Sector Geometry Exists
-- statement:
--   Let $G$ be a finite simple graph, let $D$ be a crossing-free ordinary
--   polygonal drawing of $G$, and let $A$ be dart-arc data
--   `PlaneDrawingDartArcData`.  Then there exists a dart
--   vertex-sector geometry package `PlaneDrawingDartVertexSectorGeometry`
--   for $G,D,A$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PlaneDrawingDartVertexSectorGeometryExists`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneDrawingDartVertexSectorGeometryExists.lean#L1-L30

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_OrdinaryPolygonalDrawing
import Definitions.Def_PlaneDrawingDartArcData
import Definitions.Def_PlaneDrawingDartVertexSectorGeometry

open Classical
noncomputable section

lemma PlaneDrawingDartVertexSectorGeometryExists {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (A : PlaneDrawingDartArcData G D) :
    Nonempty (PlaneDrawingDartVertexSectorGeometry G D A) := by sorry
