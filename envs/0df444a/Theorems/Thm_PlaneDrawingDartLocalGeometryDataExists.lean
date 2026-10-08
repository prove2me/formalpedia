-- Prove2me | Theorems.Thm_PlaneDrawingDartLocalGeometryDataExists
-- name    : PlaneDrawingDartLocalGeometryDataExists
-- status  : Open
-- author  : @moona3k
-- created : 2026-10-04T21:58:59.623197+00:00
-- url     : https://prove2.me/theorems/dfea6093-62f4-43a3-8bbf-f1cc8164425b
-- title:
--   Plane Drawing Dart Local Geometry Data Exists
-- statement:
--   Let $G$ be a finite simple graph, let $D$ be a crossing-free ordinary
--   polygonal drawing of $G$, and fix oriented dart-arc data
--   `PlaneDrawingDartArcData`.  Then there are vertex-star data
--   `PlaneDrawingDartVertexStarData`, compatible side-strip data
--   `PlaneDrawingDartSideStripData`, and sector-witness data
--   `PlaneDrawingDartSectorWitnessData` for $D$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PlaneDrawingDartLocalGeometryDataExists`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneDrawingDartLocalGeometryDataExists.lean#L1-L19

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_OrdinaryPolygonalDrawing
import Definitions.Def_PlaneDrawingDartArcData
import Definitions.Def_PlaneDrawingDartSectorWitnessData
import Definitions.Def_PlaneDrawingDartSideStripData
import Definitions.Def_PlaneDrawingDartVertexStarData

open Classical
noncomputable section

lemma PlaneDrawingDartLocalGeometryDataExists {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (A : PlaneDrawingDartArcData G D) :
    ∃ B : PlaneDrawingDartVertexStarData G D A,
      ∃ S : PlaneDrawingDartSideStripData G D A B,
        Nonempty (PlaneDrawingDartSectorWitnessData G D A B S) := by sorry
