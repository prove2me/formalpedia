-- Prove2me | Theorems.Thm_PathsTreesFlowers_Duality_Supplement_flowered_tree_4_5
-- name    : PathsTreesFlowers.Duality.Supplement.flowered_tree_4_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T08:39:59.084657+00:00
-- url     : https://prove2.me/theorems/64a1692c-3b68-4855-b792-b3193c71e6bd
-- title:
--   4.5 (flowered-tree theorem) — Adding an edge joining two outer vertices of a planted tree produces the flower formed by that edge and the two root paths
-- statement:
--   Let $J$ be a planted tree for a matching $M$ in a finite loopless multigraph $G$, with root $r$. Let $e$ join outer vertices $u,v$ of $J$, and let $P_u,P_v$ be their root paths. Their actual union is a flower:
--   $$\{e\}\cup P_u\cup P_v=B\cup S.$$
--
--   Here $B$ is an odd circuit maximally matched by $M\cap B$, with exposed base $b$, and $S$ is a stem from $r$ to $b$ meeting $B$ only at $b$. The edge $e$ belongs to the blossom. Equality holds for both vertex and edge sets. The stem may be the single vertex $r$. This identifies the blossom of the flowered tree used in contraction.
--
--   Differences from the source:
--   - encoding: the union of e and the two paths is a flower → a blossom and stem with exact vertex and edge unions, with e in the blossom and the stem rooted at r; reason: 4.5 and its proof identify precisely this decomposition; the published IsFlower supplies the blossom and intersection conditions
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), p. 455, 4.5 (flowered-tree theorem)

import Mathlib
import Definitions.Def_PathsTreesFlowers_Duality_Supplement_Trees

namespace PathsTreesFlowers.Duality.Supplement

open EdmondsMatching65.Polyhedron (IsMatching)

theorem flowered_tree_4_5 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (hM : IsMatching G M) (J : AltTree G) (r : V) (e : E) (u v : V)
    (hF : IsFloweredTree G M J r e u v) :
    ∃ bv be b sv se, IsRootPathFlower G M J r e u v bv be b sv se := by sorry

end PathsTreesFlowers.Duality.Supplement
