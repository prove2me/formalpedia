-- Prove2me | Theorems.Thm_PlaneDrawingDartArcDataExists
-- name    : PlaneDrawingDartArcDataExists
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T21:04:20.704661+00:00
-- url     : https://prove2.me/theorems/705ea780-8bd0-4ee5-bc5a-d5eddd825cb6
-- title:
--   Plane Drawing Dart Arc Data Exists
-- statement:
--   Let $G$ be a finite simple graph and let $D$ be a crossing-free ordinary
--   polygonal drawing of $G$.  Then $D$ admits oriented dart-arc data in the
--   sense of `PlaneDrawingDartArcData`.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PlaneDrawingDartArcDataExists`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneDrawingDartArcDataExists.lean#L1-L131

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

lemma PlaneDrawingDartArcDataExists {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0) :
    Nonempty (PlaneDrawingDartArcData G D) := by sorry
