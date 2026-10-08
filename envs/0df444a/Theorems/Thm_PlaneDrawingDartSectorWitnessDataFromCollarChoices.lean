-- Prove2me | Theorems.Thm_PlaneDrawingDartSectorWitnessDataFromCollarChoices
-- name    : PlaneDrawingDartSectorWitnessDataFromCollarChoices
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T21:58:47.1683+00:00
-- url     : https://prove2.me/theorems/feacebbb-57f7-4f44-a5cb-d79b455ee436
-- title:
--   Plane Drawing Dart Sector Witness Data From Collar Choices
-- statement:
--   Let $P$ be a dart collar-choice package
--   `PlaneDrawingDartCollarChoiceData`, and let $S$ be dart
--   side-strip data whose left strip for each dart is the exported left strip
--   stored in $P$.  Then $S$ admits sector-witness data
--   `PlaneDrawingDartSectorWitnessData`.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PlaneDrawingDartSectorWitnessDataFromCollarChoices`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneDrawingDartSectorWitnessDataFromCollarChoices.lean#L1-L49

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
import Mathlib.Analysis.Convex.PathConnected
import Definitions.Def_OrdinaryPolygonalDrawing
import Definitions.Def_PlaneDrawingDartArcData
import Definitions.Def_PlaneDrawingDartCollarChoiceData
import Definitions.Def_PlaneDrawingDartSectorWitnessData
import Definitions.Def_PlaneDrawingDartSideStripData
import Definitions.Def_PlaneDrawingDartVertexSectorGeometry

open Classical
noncomputable section

lemma PlaneDrawingDartSectorWitnessDataFromCollarChoices {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (A : PlaneDrawingDartArcData G D)
    (C : PlaneDrawingDartVertexSectorGeometry G D A)
    (P : PlaneDrawingDartCollarChoiceData G D A C)
    (S : PlaneDrawingDartSideStripData G D A C.star)
    (hleft : ∀ d : G.Dart, S.leftSideStrip d = (P.sideStrips d).leftStrip) :
    Nonempty (PlaneDrawingDartSectorWitnessData G D A C.star S) := by sorry
