-- Prove2me | Theorems.Thm_SecSampling_lemma_13
-- name    : SecSampling.lemma_13
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T05:32:29.747206+00:00
-- url     : https://prove2.me/theorems/578b59f9-de87-4c2e-a287-75b7e4264b51
-- title:
--   Lemma 13 — a selection probability $q$ leaves at most $1-q$ to every descendant
-- statement:
--   Let $q$ be a (possibly randomized) strategy for the last zero problem. If $q$ has selection probability $\pi$ on an instance $I$ (it wins in $I$ with probability $\pi$), then its probability of winning in any descendant of $I$ is at most $1-\pi$.
--
--   This is the randomized analogue of Lemma 7.
--
--   Differences from the source:
--   - encoding: a randomized algorithm for the last zero problem → a function q m h ∈ [0, 1], the stopping probability given the norm m and the prefix h seen so far; reason: behavioural randomization is equivalent to any external randomness under perfect recall (Kuhn); it is one probability per information state of Definition 1
-- source:
--   J. Correa, A. Cristi, L. Feuilloley, T. Oosterwijk & A. Tsigonias-Dimitriadis, The Secretary Problem with Independent Sampling, arXiv:2011.07869v1, https://arxiv.org/abs/2011.07869v1, Lemma 13, p.18 (PDF p.19)

import Mathlib
import Definitions.Def_SecSampling_ConflictGraph

namespace SecSampling

/-- **Lemma 13** (arXiv:2011.07869v1, p.18). If for some instance `I` a (randomized) last-zero
strategy has selection probability `q` (its probability of winning in `I`), then its probability
of winning at any descendant of `I` is at most `1 − q`. -/
theorem lemma_13 (q : LZStrategy) (hq : IsLZStrategy q) (I J : List Bool)
    (hIJ : IsDescendant I J) :
    winLZ q J ≤ 1 - winLZ q I := by sorry

end SecSampling
