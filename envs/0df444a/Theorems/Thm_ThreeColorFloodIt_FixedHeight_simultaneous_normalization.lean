-- Prove2me | Theorems.Thm_ThreeColorFloodIt_FixedHeight_simultaneous_normalization
-- name    : ThreeColorFloodIt.FixedHeight.simultaneous_normalization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:32.330109+00:00
-- url     : https://prove2.me/theorems/a097c6cb-b3fc-4d3b-a8d4-f0142cd6eca2
-- title:
--   Lemma 7 — Simultaneous normalization
-- statement:
--   Let $G$ be a finite nonempty connected graph, with target coloring $f$ using at most three available colors. There is an optimal painting plan $(S_i,c_i)$ whose first region is the whole graph, whose intersecting later regions are contained in earlier ones, and whose strokes are all saturated against $f$:
--   $$i<j,\ S_i\cap S_j\ne\varnothing\ \Longrightarrow\ S_j\subseteq S_i,\qquad \partial S_i\cap f^{-1}(c_i)=\varnothing.$$
--   Writing $A_i$ for the vertices last painted at step $i$, the first later stroke touching each connected component of $G[S_i\setminus A_i]$ has exactly that component as its region. All four properties hold simultaneously. This supplies normalized optimum trees without assuming normalization as input.
--
--   Differences from the source:
--   - generalization: the Section 4 grid setup → every finite nonempty connected simple graph with three available colors; reason: the normalization and edge arguments use only graph connectivity, nesting and saturation, with no grid-specific step
--   - encoding: finite graphs, vertices, colors and finite rooted trees → Mathlib simple graphs, finite named carriers, a shared rooted-tree model and explicit legal-sequence predicates; reason: the same source instances are represented; unused palette colors and unowned tree nodes remain allowed
-- source:
--   Zhou, Three-Color Free-Flood-It on Fixed-Height Grids Is Polynomial-Time Solvable, STOC 2027 submission #31, supplied 2026 preprint, SHA-256 222ec38f7c30952eda9e86f87b16e8d7dfc93aa0b6b9705ac931e1b56017d280, printed p. 7 (PDF 8), Lemma 7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/31.pdf

import Definitions.Def_ThreeColorFloodIt_FixedHeight_game

set_option autoImplicit false

namespace ThreeColorFloodIt.FixedHeight

theorem simultaneous_normalization {V : Type} [Fintype V]
    (G : SimpleGraph V) (f : V → Fin 3) (connected : ConnectedSet G Set.univ) :
    ∃ ps : List (Stroke V (Fin 3)), OptimalPainting G f ps ∧ Normalized G f ps := by sorry

end ThreeColorFloodIt.FixedHeight
