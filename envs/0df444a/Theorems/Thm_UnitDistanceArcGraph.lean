-- Prove2me | Theorems.Thm_UnitDistanceArcGraph
-- name    : UnitDistanceArcGraph
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-26T19:52:05.036688+00:00
-- url     : https://prove2.me/theorems/e1c49365-fd2a-4513-b309-c99ba301b92c
-- title:
--   The unit-distance arc graph construction
-- statement:
--   For every finite point set $P$ in the Euclidean plane, there is a simple graph $G$ whose vertex type is the finite set $P$ and whose edge set is finite such that
--
--   $$
--   \operatorname{unitDist}(P)-|P|\le |E(G)|,\qquad\operatorname{cr}(G)\le 2|P|^2.
--   $$
--
--   The graph is obtained from the unit-distance relations by selecting polygonal arcs and then replacing the resulting geometric arcs by an ordinary polygonal drawing. Thus its edge count records the unit-distance count up to the vertex correction, while its crossing number is controlled quadratically by the size of $P$. This construction is the geometric bridge that allows the crossing lemma to be applied to unit distances.
--
--   **Formalization Note** Lean represents the finite point set as a `Finset`, regards `G` as a graph on the subtype of elements of `P`, and records finiteness of the graph edge set with an explicit `Fintype G.edgeSet` instance.
-- source:
--   wpegden/crossing-consequences@8769d142033fce042f502bf2857afb6b1375b5c3, Tablet/UnitDistanceArcGraph.lean, declaration `UnitDistanceArcGraph`, lines 15–18: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/UnitDistanceArcGraph.lean#L15-L18

import Definitions.Def_CrossingNumber
import Definitions.Def_unitDist

open Classical
open scoped Real
noncomputable section

lemma UnitDistanceArcGraph (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    ∃ G : SimpleGraph P, ∃ (_ : Fintype G.edgeSet),
      (unitDist P : ℝ) - (P.card : ℝ) ≤ (G.edgeFinset.card : ℝ) ∧
        (CrossingNumber G : ℝ) ≤ 2 * (P.card : ℝ) ^ 2 := by sorry
