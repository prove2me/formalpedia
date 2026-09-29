-- Prove2me | Theorems.Thm_PlaneTreeNoEdgeComplementConnected
-- name    : PlaneTreeNoEdgeComplementConnected
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T18:54:32.345994+00:00
-- url     : https://prove2.me/theorems/26c73c7c-3e60-40fc-9c89-0dad83c287c1
-- title:
--   The complement of an edgeless plane-tree drawing is polygonally path connected
-- statement:
--   Let $G$ be a finite simple graph with no edges, let $D$ be an ordinary polygonal drawing of $G$, and assume that $G$ is a tree. Then the complement of the drawing image is polygonally path connected:\n\n$$\n\operatorname{PolygonallyPathConnected}\bigl(\operatorname{OrdinaryDrawingImage}(G,D)^{\mathrm c}\bigr).\n$$\n\nThis is the base case for inductive connectivity arguments on plane drawings of trees. The formal statement uses the platform definitions of an ordinary polygonal drawing, its image, and polygonal path connectedness.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneTreeNoEdgeComplementConnected.lean#L1-L149

import Definitions.Def_PlaneFaceData
import Definitions.Def_PolygonallyPathConnected
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open Classical
noncomputable section

-- [TABLET NODE: PlaneTreeNoEdgeComplementConnected]
-- Source: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneTreeNoEdgeComplementConnected.lean#L1-L149

lemma PlaneTreeNoEdgeComplementConnected {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : OrdinaryPolygonalDrawing G)
    (hTree : G.IsTree) (hNoEdges : G.edgeSet = ∅) :
    PolygonallyPathConnected ((OrdinaryDrawingImage G D)ᶜ) := by sorry
