-- Prove2me | Theorems.Thm_OrdinaryDrawingImageCompact
-- name    : OrdinaryDrawingImageCompact
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-26T22:22:25.755536+00:00
-- url     : https://prove2.me/theorems/7bb3fbba-76df-427b-9495-e76b8bd866c0
-- title:
--   Compactness of an ordinary polygonal drawing image
-- statement:
--   For a finite graph with an ordinary polygonal drawing, the drawing image—the finite set of vertex locations together with the finitely many polygonal edge carriers—is compact in the Euclidean plane.
--
--   This compactness supplies a boundedness witness for choosing a point outside the drawing image.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/OrdinaryDrawingImageCompact.lean#L1-L47

import Definitions.Def_PlaneFaceData

open Classical
noncomputable section

-- [TABLET NODE: OrdinaryDrawingImageCompact]

lemma OrdinaryDrawingImageCompact {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (D : OrdinaryPolygonalDrawing G) :
    IsCompact (OrdinaryDrawingImage G D) := by sorry
