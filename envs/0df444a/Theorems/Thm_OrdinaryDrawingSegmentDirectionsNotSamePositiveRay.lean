-- Prove2me | Theorems.Thm_OrdinaryDrawingSegmentDirectionsNotSamePositiveRay
-- name    : OrdinaryDrawingSegmentDirectionsNotSamePositiveRay
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T21:04:18.860133+00:00
-- url     : https://prove2.me/theorems/ef1154a3-cc02-430b-9c1a-5d9413cf7d1a
-- title:
--   Ordinary Drawing Segment Directions Not Same Positive Ray
-- statement:
--   In an ordinary polygonal drawing, let two distinct drawn edge arcs contain
--   listed segments $S_e$ and $S_f$.  Suppose both segments start, as
--   oriented germs, at the same point $x$, with direction vectors $d$ and
--   $v$, and $d\ne0$.  Then $v$ is not a positive scalar multiple of
--   $d$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `OrdinaryDrawingSegmentDirectionsNotSamePositiveRay`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/OrdinaryDrawingSegmentDirectionsNotSamePositiveRay.lean#L1-L39

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Definitions.Def_OrdinaryPolygonalDrawing

open Classical
noncomputable section

lemma OrdinaryDrawingSegmentDirectionsNotSamePositiveRay {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    {e f : G.edgeFinset} (hef : e ≠ f)
    {i j : ℕ}
    (hi : i + 1 < (D.edgeArc e).vertices.length)
    (hj : j + 1 < (D.edgeArc f).vertices.length)
    {x d v : EuclideanSpace ℝ (Fin 2)}
    (hd : d ≠ 0)
    (hseg_e :
      segment ℝ x (x + d) =
        segment ℝ (D.edgeArc e).vertices[i] (D.edgeArc e).vertices[i + 1])
    (hseg_f :
      segment ℝ x (x + v) =
        segment ℝ (D.edgeArc f).vertices[j] (D.edgeArc f).vertices[j + 1]) :
    ¬ ∃ a : ℝ, 0 < a ∧ v = a • d := by sorry
