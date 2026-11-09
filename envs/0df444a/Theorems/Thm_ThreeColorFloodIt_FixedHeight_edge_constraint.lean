-- Prove2me | Theorems.Thm_ThreeColorFloodIt_FixedHeight_edge_constraint
-- name    : ThreeColorFloodIt.FixedHeight.edge_constraint
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:35.664034+00:00
-- url     : https://prove2.me/theorems/e150ef22-2d44-4873-b06e-4206e51edb02
-- title:
--   Lemma 8 — Edge constraint of a normalized optimum
-- statement:
--   For an optimal simultaneously normalized painting on a finite connected graph, form its region tree $T$ and last-stroke owner map $\pi$. Every graph edge $uv$ has comparable owners. If $\pi(u)$ is a proper ancestor of $\pi(v)$, then
--   $$c(x)\ne c(\pi(u))\quad\text{for every }\pi(u)<_T x\le_T\pi(v).$$
--   The lower owner is included; the upper owner is excluded. The premise describes the region tree of the normalized plan and does not assume the edge condition being proved. This is the boundary constraint used by both local templates and legal reversal.
--
--   Differences from the source:
--   - generalization: the Section 4 grid setup → every finite nonempty connected simple graph with three available colors; reason: the normalization and edge arguments use only graph connectivity, nesting and saturation, with no grid-specific step
--   - encoding: finite graphs, vertices, colors and finite rooted trees → Mathlib simple graphs, finite named carriers, a shared rooted-tree model and explicit legal-sequence predicates; reason: the same source instances are represented; unused palette colors and unowned tree nodes remain allowed
-- source:
--   Zhou, Three-Color Free-Flood-It on Fixed-Height Grids Is Polynomial-Time Solvable, STOC 2027 submission #31, supplied 2026 preprint, SHA-256 222ec38f7c30952eda9e86f87b16e8d7dfc93aa0b6b9705ac931e1b56017d280, printed p. 8 (PDF 9), Lemma 8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/31.pdf

import Definitions.Def_ThreeColorFloodIt_FixedHeight_trees

set_option autoImplicit false

namespace ThreeColorFloodIt.FixedHeight

theorem edge_constraint {V : Type} [Fintype V] (G : SimpleGraph V)
    (f : V → Fin 3) (connected : ConnectedSet G Set.univ)
    (ps : List (Stroke V (Fin 3))) (optimal : OptimalPainting G f ps)
    (normalized : Normalized G f ps) (T : TreeData V (Fin 3))
    (e : Fin T.tree.size ≃ Fin ps.length) (represents : RegionTreeOf ps T e) :
    EdgeConstraint G T := by sorry

end ThreeColorFloodIt.FixedHeight
