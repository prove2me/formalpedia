-- Prove2me | Theorems.Thm_PlaneFaceDataExists
-- name    : PlaneFaceDataExists
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-26T21:35:57.378373+00:00
-- url     : https://prove2.me/theorems/9121881c-4431-4cb8-a650-61ea684197f9
-- title:
--   Existence of plane face data
-- statement:
--   Every crossing-free ordinary polygonal drawing of a finite simple graph admits a plane face data record carrying the indexed faces and the associated dart, side-strip, sector, and cyclic successor information.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneFaceDataExists.lean#L1-L137

import Definitions.Def_PlaneFaceData

open Classical
noncomputable section

lemma PlaneFaceDataExists {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (hD : D.crossingSet.card = 0) :
    Nonempty (PlaneFaceData G D) := by sorry
