-- Prove2me | Theorems.Thm_SecSampling_lemma_18
-- name    : SecSampling.lemma_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:32:08.193314+00:00
-- url     : https://prove2.me/theorems/b6fea860-7b1b-4a07-b821-c068e9d26d47
-- title:
--   Lemma 18 — the nodes the $k$-max algorithm selects in the conflict graph
-- statement:
--   Let $p\in(0,1)$, $k=\lfloor 1/(1-p)\rfloor$, and consider the $k$-max strategy for the last zero problem. For every instance $I$ of size at least $k+1$, the $k$-max strategy wins in $I$ if and only if
--
--   1. $I$ has norm at least $k$,
--   2. $I$ has degree at most $k$, and
--   3. $I$ is not removed: no node of size at least $k+1$ of which $I$ is a descendant is won by $k$-max.
--
--   Thus, scanning sizes upward from $k+1$, $k$-max selects exactly the non-removed nodes of norm at least $k$ and degree at most $k$.
--
--   Differences from the source:
--   - reading: k-max "selects" a node, and "non-removed" nodes → k-max wins in the node with probability 1; non-removed = no ancestor of size ≥ k + 1 is won by k-max; reason: k-max is deterministic, so its selection probability is 0 or 1; it starts at size k + 1, so only selections from size k + 1 on remove nodes
--   - reading: the player wins if she stops on the last 0 of the sequence (Definition 1) → a string with no 0 is won by every strategy; reason: the page leaves this case open; p.2 declares it a win by vacuity for AOSp, and it changes the performance at size n by pⁿ only
-- source:
--   J. Correa, A. Cristi, L. Feuilloley, T. Oosterwijk & A. Tsigonias-Dimitriadis, The Secretary Problem with Independent Sampling, arXiv:2011.07869v1, https://arxiv.org/abs/2011.07869v1, Lemma 18, p.23 (PDF p.24)

import Mathlib
import Definitions.Def_SecSampling_ConflictGraph

namespace SecSampling

/-- **Lemma 18** (arXiv:2011.07869v1, p.23). Consider the instances of size `≥ k + 1`, with
`k = ⌊1/(1−p)⌋`, and the k-max algorithm, which starts at size `k + 1` and iteratively considers
instances of increasing size. For every size it selects (wins in) exactly the non-removed nodes
that have norm at least `k` and degree at most `k`; a node is removed when it is a descendant of a
node of size `≥ k + 1` that k-max selects. -/
theorem lemma_18 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (I : List Bool)
    (hI : kOf p + 1 ≤ I.length) :
    winLZ (kmaxLZ p) I = 1 ↔
      (kOf p ≤ bitNorm I ∧ degree I ≤ kOf p ∧
        ∀ J : List Bool, kOf p + 1 ≤ J.length → IsDescendant J I → winLZ (kmaxLZ p) J ≠ 1) := by sorry

end SecSampling
