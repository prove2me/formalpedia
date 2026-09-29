-- Prove2me | Theorems.Thm_PlaneFaceDataOneFaceOfPolygonallyPathConnectedComplement
-- name    : PlaneFaceDataOneFaceOfPolygonallyPathConnectedComplement
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-26T22:22:36.253459+00:00
-- url     : https://prove2.me/theorems/8c346449-8add-45e7-9b87-59a20e3d73ff
-- title:
--   A polygonally path-connected drawing complement has one face
-- statement:
--   Let $G$ be a finite simple graph with an ordinary polygonal drawing $D$, and let $A$ be plane-face data for that drawing. If the complement of the drawing image is polygonally path connected and nonempty, then every face component is the whole complement, so the face type has exactly one element:
--
--   $$
--   \#\,A.\mathrm{Face}=1.
--   $$
--
--   This is the topological bridge from polygonal path connectedness of a planar drawing's complement to uniqueness of its face.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneFaceDataOneFaceOfPolygonallyPathConnectedComplement.lean#L1-L67

import Definitions.Def_PlaneFaceData
import Definitions.Def_PolygonallyPathConnected

open Classical
noncomputable section

-- [TABLET NODE: PlaneFaceDataOneFaceOfPolygonallyPathConnectedComplement]

lemma PlaneFaceDataOneFaceOfPolygonallyPathConnectedComplement {V : Type*}
    [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (A : PlaneFaceData G D) :
    PolygonallyPathConnected ((OrdinaryDrawingImage G D)ᶜ) →
      ((OrdinaryDrawingImage G D)ᶜ).Nonempty →
        @Fintype.card A.Face A.faceFintype = 1 := by sorry
