-- Prove2me | Theorems.Thm_PolygonalReplacementForGeometricArcs
-- name    : PolygonalReplacementForGeometricArcs
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-26T20:22:09.303743+00:00
-- url     : https://prove2.me/theorems/b397b164-c18d-4214-9789-e68d57faf9ad
-- title:
--   Polygonal replacement for geometric arcs
-- statement:
--   Let $G$ be a finite simple graph and let $D$ be a geometric arc drawing of $G$. Then there is an ordinary polygonal drawing $D'$ of the same graph such that
--
--   $$
--   |\operatorname{crossingSet}(D')|\le \operatorname{localPairCount}(D)
--   \qquad	ext{and}\qquad
--   \operatorname{CrossingNumber}(G)\le \operatorname{localPairCount}(D).
--   $$
--
--   Thus every geometric arc drawing can be replaced by a polygonal drawing whose crossing set, and hence the graph's minimum crossing number, is controlled by the local pair count of the original drawing.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalReplacementForGeometricArcs.lean#L1-L21

import Definitions.Def_GeometricArcDrawing
import Definitions.Def_CrossingNumber

open Classical
noncomputable section

lemma PolygonalReplacementForGeometricArcs {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G) :
    ∃ D' : OrdinaryPolygonalDrawing G,
      D'.crossingSet.card ≤ D.localPairCount ∧
        CrossingNumber G ≤ D.localPairCount := by sorry
