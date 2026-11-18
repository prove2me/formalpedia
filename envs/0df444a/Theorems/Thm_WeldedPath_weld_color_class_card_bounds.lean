-- Prove2me | Theorems.Thm_WeldedPath_weld_color_class_card_bounds
-- name    : WeldedPath.weld_color_class_card_bounds
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-11-17T18:27:59.897031+00:00
-- url     : https://prove2.me/theorems/a587b504-40e2-49ea-94d3-5ca375774e50
-- title:
--   Uniform bounds on the sizes of welded-tree color classes
-- statement:
--   In any valid properly three-colored welded-tree instance of height $n\ge1$, each weld-color class has between $2^{n-1}$ and $2^n$ edges. The bound holds for every color and every middle-column parameter $l$. The formal statement uses the original colored edge set, so it also bounds the size of each matching coordinate in the product distribution.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, https://arxiv.org/html/2611.05912v1#S3.SS1, Lemma 3.2 and equation (22); see also Section 4.4, the definition of m_eta before equation (76). This is a coarse explicit consequence of those counts. The supplied proof instead uses proper coloring, leaf sibling pairs, and endpoint injections, and works for every n>=1 without a parity hypothesis.

import Definitions.Def_WeldedPath_bEdge

namespace WeldedPath

theorem weld_color_class_card_bounds (n l : ℕ) (G : WeldedInstance n) (hG : G.IsValid)
    (hn : 1 ≤ n) (α : Fin 3) :
    2 ^ (n - 1) ≤ (G.classEdges l (.wld α)).card ∧
      (G.classEdges l (.wld α)).card ≤ 2 ^ n := by
  sorry

end WeldedPath
