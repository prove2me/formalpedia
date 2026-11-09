-- Prove2me | Theorems.Thm_RandOnlineSetCover_InfoLB_lemma_3_4
-- name    : RandOnlineSetCover.InfoLB.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:39:32.638927+00:00
-- url     : https://prove2.me/theorems/4f48dad9-4748-4ce1-9353-7c347c527224
-- title:
--   Lemma 3.4 — an expanding coloring with 512k² colors
-- statement:
--   For each positive integer $k$, the complete binary tree $T=(V,E)$ with $2k$ levels admits a coloring $\chi:V\to[512k^2]$ such that every subtree $H$ rooted at the global root with $|H|\le k^2$ satisfies
--
--   $$
--   |\chi(H)|\ge\frac{|H|}{2}.
--   $$
--
--   This is a simultaneous expansion guarantee for all eligible subtrees. The empty subtree satisfies the same inequality, with both sides zero.
--
--   Differences from the source:
--   - encoding: a height-2k tree, 512k² color labels and the inequality |χ(H)| ≥ |H|/2 → bit-word vertices with 2k levels, Fin (512k²) labels and H.card ≤ 2 * (χ(H)).card; reason: these are bijective finite encodings and the integer inequality is exactly equivalent to the displayed ratio
-- source:
--   Roie Levin, STOC 2027 submission #400 (October 2026), Lemma 3.4, p. 5. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/400.pdf

import Mathlib
import Definitions.Def_RandOnlineSetCover_InfoLB_BinaryTree

namespace RandOnlineSetCover.InfoLB

theorem lemma_3_4 (k : ℕ) (hk : 0 < k) :
    ∃ χ : BinaryVertex (2 * k) → Fin (512 * k ^ 2),
      ∀ H : Finset (BinaryVertex (2 * k)),
        IsRootedSubtree (treeRoot (2 * k) (by omega)) H → H.card ≤ k ^ 2 →
        H.card ≤ 2 * (subtreeColors χ H).card := by sorry

end RandOnlineSetCover.InfoLB
