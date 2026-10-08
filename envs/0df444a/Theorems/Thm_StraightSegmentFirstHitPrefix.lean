-- Prove2me | Theorems.Thm_StraightSegmentFirstHitPrefix
-- name    : StraightSegmentFirstHitPrefix
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:26:41.979722+00:00
-- url     : https://prove2.me/theorems/cbed9faa-f39b-40e3-b12a-6643b42bfc08
-- title:
--   Straight Segment First Hit Prefix
-- statement:
--   Let $[a,b]$ be a closed straight segment in $\mathbb R^2$, let
--   $U\subseteq\mathbb R^2$ be open, and suppose $[a,b]\subseteq U$.  Let
--   $[u,v]$ be another closed straight segment with $u\notin [a,b]$, and
--   suppose that $[u,v]\cap [a,b]$ is nonempty.  Then there is a point
--   $y\in [u,v]\cap U\setminus [a,b]$ such that the initial subsegment
--   $[u,y]$ is connected, contains $u$ and $y$, and is contained in
--   $[u,v]\setminus [a,b]$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `StraightSegmentFirstHitPrefix`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/StraightSegmentFirstHitPrefix.lean#L1-L118

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Analysis.Convex.Between
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.IntermediateValue

open Classical
noncomputable section

lemma StraightSegmentFirstHitPrefix
    (a b u v : EuclideanSpace ℝ (Fin 2))
    (U : Set (EuclideanSpace ℝ (Fin 2)))
    (hUopen : IsOpen U)
    (hsegment_subset_U : segment ℝ a b ⊆ U)
    (hu_not : u ∉ segment ℝ a b)
    (hsegment_hit :
      (segment ℝ u v ∩ segment ℝ a b).Nonempty) :
    ∃ y : EuclideanSpace ℝ (Fin 2),
      y ∈ segment ℝ u v ∧ y ∈ U ∧ y ∉ segment ℝ a b ∧
        IsConnected (segment ℝ u y) ∧
          u ∈ segment ℝ u y ∧ y ∈ segment ℝ u y ∧
            segment ℝ u y ⊆
              segment ℝ u v ∩ (segment ℝ a b)ᶜ := by sorry
