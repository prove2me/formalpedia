-- Prove2me | Theorems.Thm_PlaneDrawingDartSideStripDataFromCollarChoices
-- name    : PlaneDrawingDartSideStripDataFromCollarChoices
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T21:58:41.435085+00:00
-- url     : https://prove2.me/theorems/8d9d1a8a-ad4d-4c9c-9c1f-87a068fe174c
-- title:
--   Plane Drawing Dart Side Strip Data From Collar Choices
-- statement:
--   Let $P$ be a dart collar-choice package
--   `PlaneDrawingDartCollarChoiceData` for $A$ and $C$.  Then the
--   exported strips in $P$ determine dart side-strip data
--   `PlaneDrawingDartSideStripData` for $C.star$, and the left and
--   right strips of this datum are exactly the exported left and right strips
--   stored in $P$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PlaneDrawingDartSideStripDataFromCollarChoices`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneDrawingDartSideStripDataFromCollarChoices.lean#L1-L78

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
import Definitions.Def_PlaneDrawingDartSideStripData
import Definitions.Def_PlaneDrawingDartVertexSectorGeometry

open Classical
noncomputable section

lemma PlaneDrawingDartSideStripDataFromCollarChoices {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (A : PlaneDrawingDartArcData G D)
    (C : PlaneDrawingDartVertexSectorGeometry G D A)
    (P : PlaneDrawingDartCollarChoiceData G D A C) :
    ∃ S : PlaneDrawingDartSideStripData G D A C.star,
      (∀ d : G.Dart, S.leftSideStrip d = (P.sideStrips d).leftStrip) ∧
        (∀ d : G.Dart, S.rightSideStrip d = (P.sideStrips d).rightStrip) := by sorry
