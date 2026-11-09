-- Prove2me | Theorems.Thm_RandOnlineSetCover_InfoLB_lemma_3_3
-- name    : RandOnlineSetCover.InfoLB.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:40:39.369509+00:00
-- url     : https://prove2.me/theorems/243c4b31-5fb5-45d3-a47f-ee6a6a7e5da7
-- title:
--   Lemma 3.3 — fixed-coloring expected cost lower bound
-- statement:
--   For $k\ge1$, fix a coloring $\chi:V\to[m]$ of the complete binary tree with $2k$ levels and a fixed enumeration of every batch. Let $A$ be any deterministic online set-cover algorithm; it may know the coloring but observes only the revealed incidence prefixes. For a uniformly random root-to-leaf path,
--
--   $$
--   \mathbb E_\pi[|A(I_{\chi,\pi})|]\ge
--   \frac{k(k+1)}2\min_{\substack{H\text{ rooted at }v_1\\1\le|H|\le k^2}}
--   \frac{|\chi(H)|}{|H|}.
--   $$
--
--   The minimum measures the color expansion of small subtrees rooted at the global root. This separates the algorithmic cost statement from the existence of an expanding coloring.
--
--   Differences from the source:
--   - generalization: any canonical lexicographic order within batches → every fixed per-vertex enumeration independent of the chosen leaf; reason: the argument uses only completed batches and so includes the source order
--   - encoding: uniform path expectation and minimum over nonempty root subtrees → a finite arithmetic mean and a real infimum over sizes 1 through k²; reason: all paths have positive equal probability; the ratio set is finite and nonempty with positive denominators; finite decision tables preserve every online rule
-- source:
--   Roie Levin, STOC 2027 submission #400 (October 2026), Lemma 3.3, p. 4. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/400.pdf

import Mathlib
import Definitions.Def_RandOnlineSetCover_InfoLB_Inner

namespace RandOnlineSetCover.InfoLB

theorem lemma_3_3 (k m : ℕ) (hk : 0 < k) (O : BatchOrder k)
    (χ : BinaryVertex (2 * k) → Fin m) (A : DetAlg m (innerHorizon O)) :
    (k : ℝ) * (k + 1) / 2 * minimumColorRatio hk χ ≤ innerExpectedCost O χ A := by sorry

end RandOnlineSetCover.InfoLB
