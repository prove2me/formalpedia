-- Prove2me | Theorems.Thm_PathsTreesFlowers_Duality_Supplement_planted_paths_4_3
-- name    : PathsTreesFlowers.Duality.Supplement.planted_paths_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:37:30.708542+00:00
-- url     : https://prove2.me/theorems/d0c43c7d-a493-4fef-900d-ce8e799b4585
-- title:
--   4.3 (planted-tree path theorem) — Every alternating path inside a planted tree ending at an outer vertex with its matching edge is a subpath of that vertex’s root path
-- statement:
--   Let $J$ be a planted tree for a matching $M$ in a finite loopless multigraph $G$, with root $r$, and let $v$ be any outer vertex. There is a unique path $P_v$ oriented from $r$ to $v$ in $J$, and this path is a stem. Every alternating path $P$ inside $J$ which has $v$ and its matching end-edge at one end satisfies
--   $$P\text{ is a contiguous subpath of }P_v\text{, up to reversal}.$$
--
--   The unique root path is permitted to have zero edges when $v=r$. The path with a matching end-edge has positive length. This identifies the exact root path that the augmenting-tree and flowered-tree results use.
--
--   Differences from the source:
--   - encoding: the alternating path P_v in J joining v to the root → existence and uniqueness of the root-to-v path, its stem property, and contiguous subpath containment up to reversal; reason: 4.0 defines a tree by unique paths, and 4.3 explicitly states that each outer root path is a stem
--   - encoding: paths as subgraphs → oriented lists with every vertex and edge inside J; reason: orientation changes no source instance; MatchingEnd covers either endpoint
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), p. 455, 4.3 (planted-tree path theorem)

import Mathlib
import Definitions.Def_PathsTreesFlowers_Duality_Supplement_Paths

namespace PathsTreesFlowers.Duality.Supplement

open EdmondsMatching65.Polyhedron (IsMatching)

theorem planted_paths_4_3 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (hM : IsMatching G M) (J : AltTree G) (r : V)
    (hJ : IsPlantedTree G M J r) (v : V) (hv : v ∈ J.outer) :
    ∃ rv re, PathIn G J.toSub r v rv re ∧ IsStem G M rv re ∧
      (∀ wv we, PathIn G J.toSub r v wv we → wv = rv ∧ we = re) ∧
      ∀ pv pe, IsAlternatingPath G M pv pe → pv.toFinset ⊆ J.verts →
        pe.toFinset ⊆ J.edges → MatchingEnd M v pv pe → IsSubpath pv pe rv re := by sorry

end PathsTreesFlowers.Duality.Supplement
