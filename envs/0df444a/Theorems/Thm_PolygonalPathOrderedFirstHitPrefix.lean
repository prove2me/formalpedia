-- Prove2me | Theorems.Thm_PolygonalPathOrderedFirstHitPrefix
-- name    : PolygonalPathOrderedFirstHitPrefix
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:26:44.880982+00:00
-- url     : https://prove2.me/theorems/419c7d83-675a-48fa-8b14-1f21c82e8169
-- title:
--   Polygonal Path Ordered First Hit Prefix
-- statement:
--   Let $\gamma$ be a polygonal path in the sense of
--   `PolygonalPath`.  Let $[a,b]$ be a closed straight segment, and
--   let $U\subseteq\mathbb R^2$ be open with $[a,b]\subseteq U$.  If
--   $\gamma.source\notin [a,b]$ and $\gamma.target\in [a,b]$, then there are
--   a point $y$ and a set $P$ such that
--   $$
--     y\in \gamma.carrier\cap U\setminus [a,b],
--   $$
--   $$
--     P \text{ is connected},\qquad
--     \gamma.source\in P,\qquad y\in P,
--   $$
--   and
--   $$
--     P\subseteq \gamma.carrier\setminus [a,b].
--   $$
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PolygonalPathOrderedFirstHitPrefix`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalPathOrderedFirstHitPrefix.lean#L1-L140

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Analysis.Convex.Between
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_PolygonalPath

open Classical
noncomputable section

lemma PolygonalPathOrderedFirstHitPrefix
    (γ : PolygonalPath)
    (a b : EuclideanSpace ℝ (Fin 2))
    (U : Set (EuclideanSpace ℝ (Fin 2)))
    (hUopen : IsOpen U)
    (hsegment_subset_U : segment ℝ a b ⊆ U)
    (hsource_not : γ.source ∉ segment ℝ a b)
    (htarget_mem : γ.target ∈ segment ℝ a b) :
    ∃ (y : EuclideanSpace ℝ (Fin 2)) (P : Set (EuclideanSpace ℝ (Fin 2))),
      y ∈ γ.carrier ∧ y ∈ U ∧ y ∉ segment ℝ a b ∧
        IsConnected P ∧ γ.source ∈ P ∧ y ∈ P ∧
          P ⊆ γ.carrier ∩ (segment ℝ a b)ᶜ := by sorry
