-- Prove2me | Theorems.Thm_ThreeColorFloodIt_FixedHeight_painting_equivalence
-- name    : ThreeColorFloodIt.FixedHeight.painting_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:35.73476+00:00
-- url     : https://prove2.me/theorems/dc088848-654c-4001-99c2-d7e1429b4f50
-- title:
--   Proposition 1 — Painting equivalence
-- statement:
--   Let $G$ be a finite nonempty connected simple graph and $f$ a prescribed coloring from a finite available palette. Let $p(G,f)$ be the minimum connected-stroke painting cost and $F(G,f)$ the minimum legal free-flooding cost. Then
--   $$p(G,f)=F(G,f)+1.$$
--   This is the exact offset needed to transfer painting optimization to flooding. Infeasible values are represented by infinity, although connected finite inputs admit finite optima.
--
--   Differences from the source:
--   - encoding: finite graphs, vertices, colors and finite rooted trees → Mathlib simple graphs, finite named carriers, a shared rooted-tree model and explicit legal-sequence predicates; reason: the same source instances are represented; unused palette colors and unowned tree nodes remain allowed
-- source:
--   Zhou, Three-Color Free-Flood-It on Fixed-Height Grids Is Polynomial-Time Solvable, STOC 2027 submission #31, supplied 2026 preprint, SHA-256 222ec38f7c30952eda9e86f87b16e8d7dfc93aa0b6b9705ac931e1b56017d280, printed p. 5 (PDF 6), Proposition 1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/31.pdf

import Definitions.Def_ThreeColorFloodIt_FixedHeight_game

set_option autoImplicit false

namespace ThreeColorFloodIt.FixedHeight

theorem painting_equivalence {V C : Type} [Fintype V] [Fintype C]
    (G : SimpleGraph V) (f : V → C) (connected : ConnectedSet G Set.univ) :
    paintOpt G f = floodOpt G f + 1 := by sorry

end ThreeColorFloodIt.FixedHeight
