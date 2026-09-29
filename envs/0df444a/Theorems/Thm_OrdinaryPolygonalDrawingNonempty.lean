-- Prove2me | Theorems.Thm_OrdinaryPolygonalDrawingNonempty
-- name    : OrdinaryPolygonalDrawingNonempty
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-26T20:44:35.496431+00:00
-- url     : https://prove2.me/theorems/d931d833-3994-4abf-82d1-abdf53ef822c
-- title:
--   Existence of an ordinary polygonal drawing
-- statement:
--   Every finite simple graph admits at least one ordinary polygonal drawing:
--
--   $$
--   \operatorname{Nonempty}(\operatorname{OrdinaryPolygonalDrawing}(G)).
--   $$
--
--   The result provides the nonemptiness needed to take a minimum over drawing crossing sets. It is a structural existence statement, independent of any crossing-number bound.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/OrdinaryPolygonalDrawingNonempty.lean#L1-L40

import Definitions.Def_OrdinaryPolygonalDrawing

open Classical
noncomputable section

lemma OrdinaryPolygonalDrawingNonempty {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] :
    Nonempty (OrdinaryPolygonalDrawing G) := by sorry
