-- Prove2me | Theorems.Thm_PlaneDrawingDartCollarChoiceDataExists
-- name    : PlaneDrawingDartCollarChoiceDataExists
-- status  : Open
-- author  : @moona3k
-- created : 2026-10-04T21:58:21.857693+00:00
-- url     : https://prove2.me/theorems/0c6c245c-e92d-4abe-b0b7-164fa9e67902
-- title:
--   Plane Drawing Dart Collar Choice Data Exists
-- statement:
--   Let $G$ be a finite simple graph, let $D$ be a crossing-free ordinary
--   polygonal drawing of $G$, let $A$ be dart-arc data, and let $C$ be a
--   dart vertex-sector geometry package.  Then there exists a dart
--   collar-choice package `PlaneDrawingDartCollarChoiceData` for
--   $A$ and $C$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PlaneDrawingDartCollarChoiceDataExists`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneDrawingDartCollarChoiceDataExists.lean#L1-L601

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.PathConnected
import Definitions.Def_OrdinaryPolygonalDrawing
import Definitions.Def_PlaneDrawingDartArcData
import Definitions.Def_PlaneDrawingDartCollarChoiceData
import Definitions.Def_PlaneDrawingDartVertexSectorGeometry

open Classical
noncomputable section

lemma PlaneDrawingDartCollarChoiceDataExists {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (A : PlaneDrawingDartArcData G D)
    (C : PlaneDrawingDartVertexSectorGeometry G D A) :
    Nonempty (PlaneDrawingDartCollarChoiceData G D A C) := by sorry
