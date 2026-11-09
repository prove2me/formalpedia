-- Prove2me | Theorems.Thm_ThreeColorFloodIt_FixedHeight_direct_reversal
-- name    : ThreeColorFloodIt.FixedHeight.direct_reversal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:17.119271+00:00
-- url     : https://prove2.me/theorems/573571f9-58c4-4ccb-9a99-5c26894a84b2
-- title:
--   Lemma 10 — Direct reversal in every parent-before-child order
-- statement:
--   Let $T$ be any admissible painting tree for a finite connected graph with prescribed coloring $f$. For every parent-before-child order, its strokes paint $f$, and all nonroot strokes, in reverse order, are legal flooding moves:
--   $$\text{number of reverse moves}=|V(T)|-1.$$
--   Each reversed stroke recolors its entire maximal monochromatic component to its parent's different color. Only the root stroke is omitted, and the final color is the root's color. The one-node tree gives the empty flooding sequence. This supplies the actual optimal witness after painting minimization.
--
--   Differences from the source:
--   - generalization: the Section 4 grid setup → every finite nonempty connected simple graph with three available colors; reason: the normalization and edge arguments use only graph connectivity, nesting and saturation, with no grid-specific step
--   - encoding: finite graphs, vertices, colors and finite rooted trees → Mathlib simple graphs, finite named carriers, a shared rooted-tree model and explicit legal-sequence predicates; reason: the same source instances are represented; unused palette colors and unowned tree nodes remain allowed
--   - generalization: the parent-before-child painting can be reversed, except for the root stroke, by |V(T)|−1 legal flooding moves → also states that the parent-before-child painting produces f, and that the i-th reversed move recolors exactly the region S_x of the i-th reversed nonroot node to its parent's color; reason: the first is the sentence before Lemma 10 that the lemma presupposes; the second is how the source proof's moves are defined; the source's conclusion follows
-- source:
--   Zhou, Three-Color Free-Flood-It on Fixed-Height Grids Is Polynomial-Time Solvable, STOC 2027 submission #31, supplied 2026 preprint, SHA-256 222ec38f7c30952eda9e86f87b16e8d7dfc93aa0b6b9705ac931e1b56017d280, printed p. 8 (PDF 9), Lemma 10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/31.pdf

import Definitions.Def_ThreeColorFloodIt_FixedHeight_trees

set_option autoImplicit false

namespace ThreeColorFloodIt.FixedHeight

theorem direct_reversal {V : Type} [Fintype V] (G : SimpleGraph V)
    (f : V → Fin 3) (connected : ConnectedSet G Set.univ)
    (T : TreeData V (Fin 3)) (admissible : Admissible G f T)
    (order : List (Fin T.tree.size)) (parent_first : ParentOrder T order) :
    Paints G f (TreePlan T order) ∧
    Reverses G T ((order.filter fun x => x ≠ T.tree.root).reverse) f ∧
    ((order.filter fun x => x ≠ T.tree.root).reverse).length = T.tree.size - 1 := by sorry

end ThreeColorFloodIt.FixedHeight
