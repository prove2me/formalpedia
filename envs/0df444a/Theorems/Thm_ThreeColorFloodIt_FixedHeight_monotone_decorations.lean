-- Prove2me | Theorems.Thm_ThreeColorFloodIt_FixedHeight_monotone_decorations
-- name    : ThreeColorFloodIt.FixedHeight.monotone_decorations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:46.645821+00:00
-- url     : https://prove2.me/theorems/8d4ce230-8bce-421a-b622-6b4d14f1278b
-- title:
--   Lemma 16 — Monotone true prefix partitions
-- statement:
--   For true processed-region connectivity, suppose $x$ is an ancestor of $y$ and both frontier domains equal a nonempty set $D$. Then the descendant partition refines the ancestor partition. Along any chain toward the root with this fixed domain,
--   $$\#\{\text{strict partition changes}\}\le |D|-1.$$
--   The partitions are defined from actual paths in the processed regions. Arbitrary region owner data suffice for this inclusion statement; global connectivity is unnecessary. This gives the full monotone-partition representation used at every height.
--
--   Differences from the source:
--   - generalization: the three-row setup in Section 4 → all positive heights and widths with full connectivity partitions; reason: Section 5.1 explicitly carries these invariants and arguments to every height; height three is an instance
--   - generalization: decorations of the admissible painting under construction → true prefix partitions for arbitrary finite rooted owner data; reason: descendant region inclusion alone proves refinement and the block-merge bound; every admissible painting is included
--   - encoding: finite graphs, vertices, colors and finite rooted trees → Mathlib simple graphs, finite named carriers, a shared rooted-tree model and explicit legal-sequence predicates; reason: the same source instances are represented; unused palette colors and unowned tree nodes remain allowed
-- source:
--   Zhou, Three-Color Free-Flood-It on Fixed-Height Grids Is Polynomial-Time Solvable, STOC 2027 submission #31, supplied 2026 preprint, SHA-256 222ec38f7c30952eda9e86f87b16e8d7dfc93aa0b6b9705ac931e1b56017d280, printed p. 12 (PDF 13), Lemma 16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/31.pdf

import Definitions.Def_ThreeColorFloodIt_FixedHeight_connectivity

set_option autoImplicit false

namespace ThreeColorFloodIt.FixedHeight

theorem monotone_decorations {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (T : TreeData (Cell k n) (Fin 3)) (j : Fin n) :
    (∀ x y, Ancestor T.tree x y → Frontier T j x = Frontier T j y →
      Refines (PrefixPartition T j y) (PrefixPartition T j x)) ∧
    (∀ (D : Set (Fin k)) (xs : List (Fin T.tree.size)), D.Nonempty →
      (∀ x ∈ xs, Frontier T j x = D) →
      xs.IsChain (fun y x => Ancestor T.tree x y) →
      Nat.card {i : Fin (xs.length - 1) //
        PrefixPartition T j (xs.getD i.val T.tree.root) ≠
          PrefixPartition T j (xs.getD (i.val + 1) T.tree.root)} ≤ D.ncard - 1) := by sorry

end ThreeColorFloodIt.FixedHeight
