-- Prove2me | Theorems.Thm_SumFaceDegrees
-- name    : SumFaceDegrees
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-26T21:36:00.089915+00:00
-- url     : https://prove2.me/theorems/e70f2385-7e7e-44b5-86a8-f9f83344937e
-- title:
--   Sum of plane face degrees
-- statement:
--   The sum of the degrees of all indexed faces in crossing-free plane face data equals twice the number of graph edges, since each edge contributes two darts.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/SumFaceDegrees.lean#L1-L41

import Definitions.Def_PlaneFaceData

open Classical
noncomputable section

lemma SumFaceDegrees {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (hD : D.crossingSet.card = 0) (A : PlaneFaceData G D) :
    ((@Finset.univ A.Face A.faceFintype).sum A.faceDegree) =
      2 * G.edgeFinset.card := by sorry
