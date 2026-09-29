-- Prove2me | Theorems.Thm_PlaneTreeOneFace
-- name    : PlaneTreeOneFace
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-26T22:12:31.627864+00:00
-- url     : https://prove2.me/theorems/c898f750-2644-4636-a882-9a9ce24e8c8a
-- title:
--   A plane tree has one face
-- statement:
--   Let $G$ be a finite simple graph with finite edge set and decidable adjacency, let $D$ be an ordinary polygonal drawing of $G$ with no crossings, and let $A$ be plane-face data for $G$ and $D$. If $G$ is a tree, then the face type carried by $A$ has exactly one element:
--
--   $$
--   \#\,A.\mathrm{Face}=1.
--   $$
--
--   Thus a crossing-free drawing of a tree has a single complementary face in the plane-face decomposition.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneTreeOneFace.lean#L1-L42

import Definitions.Def_PlaneFaceData
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open Classical
noncomputable section

-- [TABLET NODE: PlaneTreeOneFace]

lemma PlaneTreeOneFace {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (hD : D.crossingSet.card = 0) (A : PlaneFaceData G D) :
    G.IsTree → @Fintype.card A.Face A.faceFintype = 1 := by sorry
