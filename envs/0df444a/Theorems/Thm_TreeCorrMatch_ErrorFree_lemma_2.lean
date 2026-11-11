-- Prove2me | Theorems.Thm_TreeCorrMatch_ErrorFree_lemma_2
-- name    : TreeCorrMatch.ErrorFree.lemma_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:24:41.210917+00:00
-- url     : https://prove2.me/theorems/d5736a0a-69a4-4d6e-a7af-329e0019d405
-- title:
--   Lemma 2 — $S_q(Z)=\mathrm{per}(A_q(Z))/((c-q)!(\tilde c-q)!)$
-- statement:
--   Let $Z$ be a nonnegative $c\times\tilde c$ matrix and $q\in[0:\min\{c,\tilde c\}]$. With the $(c+\tilde c-q)\times(c+\tilde c-q)$ augmented matrix $A_q(Z)$ of (13),
--
--   $$S_q(Z)=\frac{\mathrm{per}(A_q(Z))}{(c-q)!\,(\tilde c-q)!}.$$
--
--   The identity, from [42, Theorem 2.1], turns each matching sum of the likelihood-ratio recursion into the permanent of a nonnegative matrix, which a randomized approximation scheme can estimate.
--
--   Differences from the source:
--   - encoding: index sets [1 : c], [1 : c̃] and injections Inj([1:q],[1:c]) → Fin c, Fin c' and embeddings Fin q ↪ Fin c; reason: Lean convention; same instances
-- source:
--   Cheng, Wang, Ying, Near-Quadratic Error-Free Graph Matching above Otter's Threshold via Approximate Local Tree Correlation Testing, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), p. 10, Lemma 2 (PDF p. 12); proof pp. 33–34 (PDF pp. 35–36)

import Mathlib
import Definitions.Def_TreeCorrMatch_ErrorFree_MatchingSum

namespace TreeCorrMatch.ErrorFree

theorem lemma_2 (c c' : ℕ) (Z : Matrix (Fin c) (Fin c') ℝ) (hZ : ∀ i j, 0 ≤ Z i j) (q : ℕ)
    (hq : q ≤ min c c') :
    matchingSum Z q =
      (augMatrix Z q).permanent / ((c - q).factorial * (c' - q).factorial : ℝ) := by sorry

end TreeCorrMatch.ErrorFree
