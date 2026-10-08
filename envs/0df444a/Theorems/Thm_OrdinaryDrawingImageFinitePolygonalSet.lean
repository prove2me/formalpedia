-- Prove2me | Theorems.Thm_OrdinaryDrawingImageFinitePolygonalSet
-- name    : OrdinaryDrawingImageFinitePolygonalSet
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T21:04:04.093322+00:00
-- url     : https://prove2.me/theorems/eae0ccc6-034c-4d9b-8676-b9130a03012d
-- title:
--   Ordinary Drawing Image Finite Polygonal Set
-- statement:
--   For every ordinary polygonal drawing $D$ of a finite graph $G$, the drawing
--   image $|D|$ admits a finite polygonal-set presentation in the sense of
--   `FinitePolygonalSet`.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `OrdinaryDrawingImageFinitePolygonalSet`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/OrdinaryDrawingImageFinitePolygonalSet.lean#L1-L285

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Definitions.Def_FinitePolygonalSet
import Definitions.Def_OrdinaryPolygonalDrawing
import Definitions.Def_PlaneFaceData

open Classical
noncomputable section

lemma OrdinaryDrawingImageFinitePolygonalSet {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : OrdinaryPolygonalDrawing G) :
    ∃ K : FinitePolygonalSet, K.carrier = OrdinaryDrawingImage G D := by sorry
