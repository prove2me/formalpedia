-- Prove2me | Theorems.Thm_UnitDistanceArcSelectionDrawing
-- name    : UnitDistanceArcSelectionDrawing
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-26T20:22:17.89132+00:00
-- url     : https://prove2.me/theorems/f9e5bf37-dafa-4990-8283-9ea4fb728f78
-- title:
--   Unit-distance arc selection drawing
-- statement:
--   For every finite set $P$ of points in the Euclidean plane, there exist a simple graph $G$ whose vertices are the points of $P$, a finite edge-set instance for $G$, and a geometric arc drawing $D$ of $G$ such that
--
--   $$
--   \operatorname{unitDist}(P)-|P|\le |E(G)|
--   \qquad	ext{and}\qquad
--   \operatorname{localPairCount}(D)\le 2|P|^2.
--   $$
--
--   The first inequality says that the graph retains all but at most $|P|$ of the unit-distance incidences, while the second bounds the total number of local edge-branch pairs at geometric intersection points. This is the geometric selection step used before polygonally replacing the arcs.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/UnitDistanceArcSelectionDrawing.lean#L1-L20

import Definitions.Def_GeometricArcDrawing
import Definitions.Def_unitDist

open Classical
open scoped BigOperators
open scoped Real
noncomputable section

lemma UnitDistanceArcSelectionDrawing (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    ∃ G : SimpleGraph P, ∃ (_ : Fintype G.edgeSet), ∃ D : GeometricArcDrawing G,
      (unitDist P : ℝ) - (P.card : ℝ) ≤ (G.edgeFinset.card : ℝ) ∧
        (D.localPairCount : ℝ) ≤ 2 * (P.card : ℝ) ^ 2 := by sorry
