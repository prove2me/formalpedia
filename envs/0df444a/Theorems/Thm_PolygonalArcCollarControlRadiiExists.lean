-- Prove2me | Theorems.Thm_PolygonalArcCollarControlRadiiExists
-- name    : PolygonalArcCollarControlRadiiExists
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T22:47:27.267987+00:00
-- url     : https://prove2.me/theorems/38768466-fbaf-4579-91f7-01911f05d620
-- title:
--   Existence of collar-control radii for a polygonal arc
-- statement:
--   For every polygonal arc $\gamma$ and every positive tolerance $\eta$, there is a family of positive radii, one at each vertex, that is smaller than $\eta$, has pairwise disjoint closed vertex balls, has adjacent radii summing to less than the corresponding edge length, and has every vertex ball disjoint from each nonincident edge. In symbols,
--
--   $$
--   \eta>0\quad\Longrightarrow\quad
--   \operatorname{Nonempty}(\operatorname{PolygonalArcCollarControlRadii}(\gamma,\eta)).
--   $$
--
--   These uniform collar data are the local geometric foundation for isolating the two endpoints of a simple polygonal arc.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarControlRadiiExists.lean#L1-L198

import Definitions.Def_PolygonalArcCollarControlRadii

open Classical
noncomputable section

lemma PolygonalArcCollarControlRadiiExists (γ : PolygonalArc) {η : ℝ}
    (hη : 0 < η) :
    Nonempty (PolygonalArcCollarControlRadii γ η) := by sorry
