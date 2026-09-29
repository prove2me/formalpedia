-- Prove2me | Theorems.Thm_OrdinaryPolygonalDrawingDeleteEdges
-- name    : OrdinaryPolygonalDrawingDeleteEdges
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-26T21:10:23.920983+00:00
-- url     : https://prove2.me/theorems/938a16b8-d407-4f92-8fab-9d50d8c4945f
-- title:
--   Deleting edges from an ordinary polygonal drawing
-- statement:
--   Let $G$ be a finite simple graph, let $D$ be an ordinary polygonal drawing of $G$, and let $S$ be a finite set of unordered vertex pairs. After deleting from $G$ every edge whose unordered pair lies in $S$, there is an ordinary polygonal drawing $D'$ of the resulting graph such that
--
--   $$
--   D'.\operatorname{crossingSet}
--   =\{p\in D.\operatorname{crossingSet}:	ext{the crossing at }p	ext{ is supported by two retained edges}\},
--   $$
--
--   where the retained-edge condition is expressed by the displayed Lean filter over the original edge finset. Moreover, the new edge count is
--
--   $$
--   |E(G\setminus S)|=|E(G)|-|S\cap E(G)|.
--   $$
--
--   This interface formalizes the operation of deleting a prescribed collection of edges while retaining the original drawing data and exactly the crossings that remain supported by undeleted edges.
--
--   **Formalization Note** Unordered edges are represented by `Sym2 V`, and the retained crossing condition is stated using the original edge finset of $G$.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/OrdinaryPolygonalDrawingDeleteEdges.lean#L1-L135

import Definitions.Def_OrdinaryPolygonalDrawing
import Mathlib.Combinatorics.SimpleGraph.Copy

open Classical
noncomputable section

lemma OrdinaryPolygonalDrawingDeleteEdges {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (D : OrdinaryPolygonalDrawing G)
    (S : Finset (Sym2 V)) :
    ∃ D' : OrdinaryPolygonalDrawing (G.deleteEdges (S : Set (Sym2 V))),
      D'.crossingSet =
          D.crossingSet.filter (fun p =>
            ∃ e₁ e₂ : G.edgeFinset,
              e₁ ≠ e₂ ∧ e₁.1 ∉ S ∧ e₂.1 ∉ S ∧
                p ∈ (D.edgeArc e₁).relativeInterior ∧
                  p ∈ (D.edgeArc e₂).relativeInterior) ∧
        (G.deleteEdges (S : Set (Sym2 V))).edgeFinset.card =
          G.edgeFinset.card - (S ∩ G.edgeFinset).card := by sorry
