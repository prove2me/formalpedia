-- Prove2me | Theorems.Thm_PlaneDrawingDartSideStripsWithSectorWitnessesExist
-- name    : PlaneDrawingDartSideStripsWithSectorWitnessesExist
-- status  : Open
-- author  : @moona3k
-- created : 2026-10-04T21:59:01.205035+00:00
-- url     : https://prove2.me/theorems/78ba2fad-e149-4789-96d5-a6f67af4d674
-- title:
--   Plane Drawing Dart Side Strips With Sector Witnesses Exist
-- statement:
--   Let $G$ be a finite simple graph, let $D$ be a crossing-free ordinary
--   polygonal drawing of $G$, let $A$ be dart-arc data, and let
--   $C$ be a dart vertex-sector geometry package
--   `PlaneDrawingDartVertexSectorGeometry`.  Then there are compatible
--   dart side-strip data `PlaneDrawingDartSideStripData` for the
--   vertex-star data $C.star$, and the resulting strips have sector witnesses
--   `PlaneDrawingDartSectorWitnessData`.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PlaneDrawingDartSideStripsWithSectorWitnessesExist`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneDrawingDartSideStripsWithSectorWitnessesExist.lean#L1-L48

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
import Definitions.Def_OrdinaryPolygonalDrawing
import Definitions.Def_PlaneDrawingDartArcData
import Definitions.Def_PlaneDrawingDartSectorWitnessData
import Definitions.Def_PlaneDrawingDartSideStripData
import Definitions.Def_PlaneDrawingDartVertexSectorGeometry

open Classical
noncomputable section

lemma PlaneDrawingDartSideStripsWithSectorWitnessesExist {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (A : PlaneDrawingDartArcData G D)
    (C : PlaneDrawingDartVertexSectorGeometry G D A) :
    ∃ S : PlaneDrawingDartSideStripData G D A C.star,
      Nonempty (PlaneDrawingDartSectorWitnessData G D A C.star S) := by sorry
