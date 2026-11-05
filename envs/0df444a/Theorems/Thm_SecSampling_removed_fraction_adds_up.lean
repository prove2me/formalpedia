-- Prove2me | Theorems.Thm_SecSampling_removed_fraction_adds_up
-- name    : SecSampling.removed_fraction_adds_up
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:32:40.885248+00:00
-- url     : https://prove2.me/theorems/8c330b10-2669-47c7-b650-562278988ae9
-- title:
--   §5.2.2 — the removed fraction adds up: selection probabilities along a monotone path sum to at most 1
-- statement:
--   Let $q$ be a (possibly randomized) strategy for the last zero problem, and write $\mathrm{win}_q(I)$ for its selection probability of $I$.
--
--   1. If $J$ is a descendant of $I$ and $K$ a descendant of $J$, then the removed fraction $q_r(K)$ (the sum of the selection probabilities of the nodes of which $K$ is a descendant) and the selection probability of $K$ satisfy
--   $$q_r(K)\ge\mathrm{win}_q(I)+\mathrm{win}_q(J),\qquad \mathrm{win}_q(K)\le 1-\mathrm{win}_q(I)-\mathrm{win}_q(J).$$
--   2. More generally, along every monotone path $P$ of the conflict graph, $\sum_{I\in P}\mathrm{win}_q(I)\le 1$; that is, the selection probabilities of any strategy form a valid fractional selection.
--
--   This is the bridge from strategies to the selections studied in Lemmas 17 and 20: the performance of $q$ at size $n$ is the performance of its selection.
--
--   Differences from the source:
--   - reading: for any descendant of the second instance its removed fraction is q + r and its selection probability is at most 1 − q − r → its removed fraction is at least q + r and its selection probability is at most 1 − q − r; reason: the removed fraction also contains the selection probabilities of the other ancestors of the descendant, so equality holds only when those vanish
--   - generalization: two nested descendants (three nodes) → every monotone path: the selection probabilities sum to at most 1; reason: this is the validity notion of p.25 used by Lemmas 17 and 20; for a three-node path it gives clause 1, and the paper's Lemma 11 is its deterministic case
--   - encoding: a randomized algorithm for the last zero problem → a function q m h ∈ [0, 1], the stopping probability given the norm m and the prefix h seen so far; reason: behavioural randomization is equivalent to any external randomness under perfect recall (Kuhn); it is one probability per information state of Definition 1
--   - encoding: a monotone path is a possibly infinite path (p.15) → validity is required on finite monotone paths; reason: the terms are nonnegative, so a sum over an infinite path is bounded by 1 iff all its finite partial sums are
-- source:
--   J. Correa, A. Cristi, L. Feuilloley, T. Oosterwijk & A. Tsigonias-Dimitriadis, The Secretary Problem with Independent Sampling, arXiv:2011.07869v1, https://arxiv.org/abs/2011.07869v1, §5.2.2, p.18 (PDF p.19), "this removed fraction adds up"; validity as defined on p.25

import Mathlib
import Definitions.Def_SecSampling_FractionalSelection

namespace SecSampling

/-- **The removed fraction adds up** (arXiv:2011.07869v1, §5.2.2, p.18, "this removed fraction
adds up"). For every (randomized) last-zero strategy `q`:

1. if `J` is a descendant of `I` and `K` a descendant of `J`, then, with `q` and `r` the selection
   probabilities of `I` and `J`, the removed fraction of `K` is at least `q + r` (it is exactly
   `q + r` when `I` and `J` are the only ancestors of `K` with positive selection probability)
   and the probability of winning in `K` is at most `1 − q − r`;
2. the selection probabilities of `q` form a valid fractional selection: along every monotone path
   they sum to at most `1`. -/
theorem removed_fraction_adds_up (q : LZStrategy) (hq : IsLZStrategy q) :
    (∀ I J K : List Bool, IsDescendant I J → IsDescendant J K →
      winLZ q I + winLZ q J ≤ removedFrac (winLZ q) K ∧
        winLZ q K ≤ 1 - winLZ q I - winLZ q J) ∧
    IsValidSel (winLZ q) := by sorry

end SecSampling
