-- Prove2me | Theorems.Thm_ThreeColorFloodIt_FixedHeight_local_root_marked
-- name    : ThreeColorFloodIt.FixedHeight.local_root_marked
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:24.3286+00:00
-- url     : https://prove2.me/theorems/fa781e5a-9536-449b-beb4-a7e915a44157
-- title:
--   Lemma 12 — Local root is marked
-- statement:
--   Let $B$ be a nonempty connected named window and $K$ a local tree template for its target colors. The template's root is an owner of a window vertex:
--   $$\exists v\in B,\quad \pi_B(v)=r_B.$$
--   This follows from the local template conditions, rather than being required by their definition. It controls the number of marked and branching nodes in the local representation.
--
--   Differences from the source:
--   - encoding: finite graphs, vertices, colors and finite rooted trees → Mathlib simple graphs, finite named carriers, a shared rooted-tree model and explicit legal-sequence predicates; reason: the same source instances are represented; unused palette colors and unowned tree nodes remain allowed
-- source:
--   Zhou, Three-Color Free-Flood-It on Fixed-Height Grids Is Polynomial-Time Solvable, STOC 2027 submission #31, supplied 2026 preprint, SHA-256 222ec38f7c30952eda9e86f87b16e8d7dfc93aa0b6b9705ac931e1b56017d280, printed p. 9 (PDF 10), Lemma 12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/31.pdf

import Definitions.Def_ThreeColorFloodIt_FixedHeight_trees

set_option autoImplicit false

namespace ThreeColorFloodIt.FixedHeight

theorem local_root_marked {s : ℕ} (G : SimpleGraph (Fin s)) (f : Fin s → Fin 3)
    (connected : ConnectedSet G Set.univ) (K : TreeData (Fin s) (Fin 3))
    (template : LocalTemplate G f K) : Marked K K.tree.root := by sorry

end ThreeColorFloodIt.FixedHeight
