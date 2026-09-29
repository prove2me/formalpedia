-- Prove2me | Theorems.Thm_PlanarEdgeBound
-- name    : PlanarEdgeBound
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-26T21:10:21.100504+00:00
-- url     : https://prove2.me/theorems/c07d1ffc-e204-4895-9fcb-18b18025cba8
-- title:
--   Edge bound for a graph with a crossing-free ordinary drawing
-- statement:
--   Let $G$ be a finite simple graph. If $G$ admits an ordinary polygonal drawing whose crossing set has cardinality zero, then its number of edges is at most three times its number of vertices:
--
--   $$
--   |E(G)|\le 3|V(G)|.
--   $$
--
--   This is the global planar edge bound used after removing one selected edge for each crossing point. It is stated for the drawing formalism used by the crossing-number development and includes disconnected graphs.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlanarEdgeBound.lean#L1-L64

import Definitions.Def_OrdinaryPolygonalDrawing

open Classical
noncomputable section

lemma PlanarEdgeBound {V : Type*} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet] :
    (∃ D : OrdinaryPolygonalDrawing G, D.crossingSet.card = 0) →
      G.edgeFinset.card ≤ 3 * Fintype.card V := by sorry
