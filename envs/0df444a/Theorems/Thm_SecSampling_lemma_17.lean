-- Prove2me | Theorems.Thm_SecSampling_lemma_17
-- name    : SecSampling.lemma_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:33:29.16014+00:00
-- url     : https://prove2.me/theorems/20b3e54b-36d8-4e96-96fd-1d76fffd54b7
-- title:
--   Lemma 17 — the fill-in strategy has optimal average performance in every window
-- statement:
--   Let $p\in(0,1)$ and consider a window $[n,n+t]$. The fill-in strategy for this window is a valid algorithm in the conflict graph, and every valid (randomized) algorithm $q_s$ has average performance in the window at most that of the fill-in strategy:
--   $$\frac{1}{t+1}\sum_{s=n}^{n+t}\ \sum_{|I|=s}p^{m(I)}(1-p)^{s-m(I)}q_s(I)\ \le\ \frac{1}{t+1}\sum_{s=n}^{n+t}\ \sum_{|I|=s}p^{m(I)}(1-p)^{s-m(I)}\,\mathrm{fill}(I).$$
--
--   Combined with Lemma 19, this bounds the window average of every strategy by that of $k$-max plus $2/(t+1)$.
--
--   Differences from the source:
--   - reading: the fill-in strategy has optimal average performance → fill-in is valid, and its window average is at least that of every valid randomized selection; reason: p.25: "extending this lemma suffices to extend the negative results to randomized algorithms"; optimality is among valid algorithms, and fill-in is one
--   - encoding: a monotone path is a possibly infinite path (p.15) → validity is required on finite monotone paths; reason: the terms are nonnegative, so a sum over an infinite path is bounded by 1 iff all its finite partial sums are
-- source:
--   J. Correa, A. Cristi, L. Feuilloley, T. Oosterwijk & A. Tsigonias-Dimitriadis, The Secretary Problem with Independent Sampling, arXiv:2011.07869v1, https://arxiv.org/abs/2011.07869v1, Lemma 17, p.22 (PDF p.23); extension to randomized algorithms, p.25

import Mathlib
import Definitions.Def_SecSampling_FractionalSelection

namespace SecSampling

/-- **Lemma 17** (arXiv:2011.07869v1, p.22). The fill-in strategy has optimal average performance
for any window `[n, n + t]`: it is a valid algorithm in the conflict graph, and every valid
(randomized) algorithm has average performance in the window at most that of the fill-in
strategy. -/
theorem lemma_17 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n t : ℕ) :
    IsValidSel (fillIn p n t) ∧
    ∀ qs : List Bool → ℝ, IsValidSel qs → windowAvg p qs n t ≤ windowAvg p (fillIn p n t) n t := by sorry

end SecSampling
