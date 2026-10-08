-- Prove2me | Theorems.Thm_SegmentSameRayInitialSubsegment
-- name    : SegmentSameRayInitialSubsegment
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T21:04:06.093279+00:00
-- url     : https://prove2.me/theorems/af371c1e-1342-4d74-ae7f-b31dd139b9ed
-- title:
--   Segment Same Ray Initial Subsegment
-- statement:
--   Let $x,d\in\mathbb R^2$, with $d\ne 0$, and let $a>0$.
--   Then the two segments from $x$ in the directions $d$ and $a d$
--   share a nondegenerate initial subsegment: there is a point $q\ne x$
--   such that
--   $$
--     [x,q]\subseteq [x,x+d]\cap [x,x+a d].
--   $$
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `SegmentSameRayInitialSubsegment`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/SegmentSameRayInitialSubsegment.lean#L1-L65

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

open Classical
noncomputable section

lemma SegmentSameRayInitialSubsegment
    (x d : EuclideanSpace ℝ (Fin 2)) (a : ℝ)
    (hd : d ≠ 0) (ha : 0 < a) :
    ∃ q : EuclideanSpace ℝ (Fin 2),
      x ≠ q ∧
        segment ℝ x q ⊆
          segment ℝ x (x + d) ∩ segment ℝ x (x + a • d) := by sorry
