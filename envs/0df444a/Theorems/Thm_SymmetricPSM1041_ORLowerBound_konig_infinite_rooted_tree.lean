-- Prove2me | Theorems.Thm_SymmetricPSM1041_ORLowerBound_konig_infinite_rooted_tree
-- name    : SymmetricPSM1041.ORLowerBound.konig_infinite_rooted_tree
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:56:54.44278+00:00
-- url     : https://prove2.me/theorems/595e8a89-e345-4d16-993f-38ad7599359d
-- title:
--   Lemma 37 — infinite path in a finitely branching rooted tree
-- statement:
--   Let $T$ be an infinite rooted tree with vertex set $V$ and root $o$. Assume that every vertex has a finite set of children. Then there is a sequence $p:\mathbb N\to V$ such that
--
--   $$p(0)=o,\qquad p\text{ is injective},\qquad p(k+1)\text{ is a child of }p(k)\quad(k\ge0).$$
--
--   Thus the tree has an infinite path starting at the root. Leaves are permitted; infinitude does not assert that each vertex extends. This is the compactness ingredient used by the source's finite Higman derivation.
--
--   Differences from the source:
--   - encoding: a rooted tree and an infinite path from its root → a reachable parent-map tree and an injective child sequence beginning at the root; reason: every rooted tree has the parent representation; the root’s self-parent is excluded from child edges
-- source:
--   Marshall Ball, Peter Crawford-Kahrl, Vladimir Podolskii, Morgan Prior, STOC 2027 submission #1041 (October 2026), p. 26, Lemma 37

import Mathlib
import Definitions.Def_SymmetricPSM1041_ORLowerBound_RootedTree

namespace SymmetricPSM1041.ORLowerBound

theorem konig_infinite_rooted_tree {V : Type*} [Infinite V] (T : RootedTree V)
    (hfinite : ∀ v, (children T v).Finite) :
    ∃ p : ℕ → V, p 0 = T.root ∧ Function.Injective p ∧
      ∀ k, p (k + 1) ∈ children T (p k) := by sorry

end SymmetricPSM1041.ORLowerBound
