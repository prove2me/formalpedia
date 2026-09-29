-- Prove2me | Theorems.Thm_PlaneTreeDrawingComplementConnected
-- name    : PlaneTreeDrawingComplementConnected
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-26T22:22:39.348967+00:00
-- url     : https://prove2.me/theorems/b67ade42-e692-412f-ad66-9424bafa2c83
-- title:
--   The complement of a crossing-free plane tree drawing is polygonally path connected
-- statement:
--   Let $G$ be a finite simple graph and $D$ an ordinary polygonal drawing with no crossings. If $G$ is a tree, then the complement of the drawing image is polygonally path connected.
--
--   This gives the inductive topological connectivity statement needed to show that a plane drawing of a tree has only one face.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneTreeDrawingComplementConnected.lean#L1-L73

import Definitions.Def_PlaneFaceData
import Definitions.Def_PolygonallyPathConnected
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open Classical
noncomputable section

universe u

-- [TABLET NODE: PlaneTreeDrawingComplementConnected]

lemma PlaneTreeDrawingComplementConnected {V : Type u} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0) :
    G.IsTree → PolygonallyPathConnected ((OrdinaryDrawingImage G D)ᶜ) := by sorry
