-- Prove2me | Theorems.Thm_TreeCorrMatch_ErrorFree_lemma_1
-- name    : TreeCorrMatch.ErrorFree.lemma_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:25:54.30714+00:00
-- url     : https://prove2.me/theorems/2471ce4f-46a7-48bf-98b4-94207dad3d89
-- title:
--   Lemma 1 — likelihood-ratio recursion $L_k=e^{\lambda s}\sum_q(1-s)^{c+\tilde c-2q}S_q(Z)$, $L_0=1$
-- statement:
--   Let $k\ge1$, $\lambda>0$ and $s\in(0,1]$. Let $t,\tilde t$ be rooted trees of depth at most $k$, and let $t_1,\dots,t_c$ and $\tilde t_1,\dots,\tilde t_{\tilde c}$ be the unlabeled subtrees rooted at the children of their roots. Define the $c\times\tilde c$ matrix $Z_{ij}=\frac s\lambda L_{k-1}(t_i,\tilde t_j)$. Then, with $0^0=1$,
--
--   $$L_k(t,\tilde t)=e^{\lambda s}\sum_{q=0}^{\min\{c,\tilde c\}}(1-s)^{c+\tilde c-2q}\,S_q(Z),$$
--
--   and at depth zero $L_0(t,\tilde t)=1$ for the unique pair of single-node trees.
--
--   This recursion is the basis of the algorithm ApproxLR, which replaces each $S_q$ by an approximated permanent.
--
--   Differences from the source:
--   - encoding: (t, t̃) ∈ Z_k × Z_k and the unlabeled child subtrees t_i, t̃_j → ordered trees t, t' of depth ≤ k, compared through cls; t_i = cls of the i-th child in list order; reason: every unlabeled tree has an ordered representative; the identity holds for every enumeration of the children
--   - encoding: node set [n] → Fin n (0-based); reason: Lean convention; same instances
-- source:
--   Cheng, Wang, Ying, Near-Quadratic Error-Free Graph Matching above Otter's Threshold via Approximate Local Tree Correlation Testing, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), p. 10, Lemma 1 (PDF p. 12); proof p. 33 (PDF p. 35)

import Mathlib
import Definitions.Def_TreeCorrMatch_ErrorFree_TreePairLaws
import Definitions.Def_TreeCorrMatch_ErrorFree_MatchingSum

namespace TreeCorrMatch.ErrorFree

theorem lemma_1 (k : ℕ) (hk : 1 ≤ k) (lam s : ℝ) (hlam : 0 < lam) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (t t' : OTree) (ht : t.depth ≤ k) (ht' : t'.depth ≤ k) :
    likelihoodRatio lam s k (cls t) (cls t') =
        Real.exp (lam * s) *
          ∑ q ∈ Finset.range (min t.children.length t'.children.length + 1),
            (1 - s) ^ (t.children.length + t'.children.length - 2 * q) *
              matchingSum
                (fun (i : Fin t.children.length) (j : Fin t'.children.length) =>
                  s / lam * likelihoodRatio lam s (k - 1) (cls (t.children.get i))
                    (cls (t'.children.get j))) q ∧
      likelihoodRatio lam s 0 (cls OTree.leaf) (cls OTree.leaf) = 1 := by sorry

end TreeCorrMatch.ErrorFree
