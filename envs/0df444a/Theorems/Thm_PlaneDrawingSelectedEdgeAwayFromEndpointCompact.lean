-- Prove2me | Theorems.Thm_PlaneDrawingSelectedEdgeAwayFromEndpointCompact
-- name    : PlaneDrawingSelectedEdgeAwayFromEndpointCompact
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T21:04:35.788755+00:00
-- url     : https://prove2.me/theorems/3f48f1d9-6afa-4917-a260-24f991d51eba
-- title:
--   Plane Drawing Selected Edge Away From Endpoint Compact
-- statement:
--   Let $D$ be a crossing-free ordinary polygonal drawing of a finite graph, let
--   $e$ be an edge, and suppose $D.edgeArc(e)=\gamma$.  For every pair of
--   positive radii $r_0,r_1$, the part of
--   $\mathrm{OrdinaryDrawingImageWithoutEdge}(G,D,e)$ outside the two endpoint
--   balls
--   $$
--     B(\gamma.source,r_0)\cup B(\gamma.target,r_1)
--   $$
--   is compact and is disjoint from $\gamma.carrier$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PlaneDrawingSelectedEdgeAwayFromEndpointCompact`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneDrawingSelectedEdgeAwayFromEndpointCompact.lean#L1-L91

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Definitions.Def_OrdinaryDrawingImageWithoutEdge
import Definitions.Def_OrdinaryPolygonalDrawing
import Definitions.Def_PolygonalArc

open Classical
noncomputable section

lemma PlaneDrawingSelectedEdgeAwayFromEndpointCompact {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (e : G.edgeFinset) (γ : PolygonalArc) :
    D.edgeArc e = γ →
      ∀ r₀ r₁ : ℝ, 0 < r₀ → 0 < r₁ →
        let A : Set (EuclideanSpace ℝ (Fin 2)) :=
          OrdinaryDrawingImageWithoutEdge G D e \
            (Metric.ball γ.source r₀ ∪ Metric.ball γ.target r₁)
        IsCompact A ∧ Disjoint A γ.carrier := by sorry
