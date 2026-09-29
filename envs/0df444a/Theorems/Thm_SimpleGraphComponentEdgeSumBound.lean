-- Prove2me | Theorems.Thm_SimpleGraphComponentEdgeSumBound
-- name    : SimpleGraphComponentEdgeSumBound
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-26T21:20:42.055407+00:00
-- url     : https://prove2.me/theorems/40878c13-741b-4ea8-8574-bc3c1e0710a2
-- title:
--   Summing edge bounds over connected components
-- statement:
--   Let $G$ be a finite simple graph. Assume that every connected component $c$ satisfies the induced-component edge bound
--
--   $$
--   |E(G[c])|\le 3|V(c)|.
--   $$
--
--   Then the whole graph satisfies
--
--   $$
--   |E(G)|\le 3|V(G)|.
--   $$
--
--   The theorem packages the finite disjoint decomposition of the vertex and edge sets into connected components.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/SimpleGraphComponentEdgeSumBound.lean#L1-L101

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Definitions.Def_OrdinaryPolygonalDrawing

open Classical
noncomputable section

lemma SimpleGraphComponentEdgeSumBound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (hcomp : ∀ c : G.ConnectedComponent,
      (G.induce c.supp).edgeFinset.card ≤ 3 * Fintype.card c.supp) :
    G.edgeFinset.card ≤ 3 * Fintype.card V := by sorry
