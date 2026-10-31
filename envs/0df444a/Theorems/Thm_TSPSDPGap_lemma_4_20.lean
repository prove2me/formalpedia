-- Prove2me | Theorems.Thm_TSPSDPGap_lemma_4_20
-- name    : TSPSDPGap.lemma_4_20
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:38:32.759592+00:00
-- url     : https://prove2.me/theorems/74bb6dd0-e4e2-4f21-9f39-45f8a5329a9d
-- title:
--   Lemma 4.20 — $\sum_{j=1}^{g-1}(g-j)\mathbb 1\{j-k\text{ odd}\}=\frac14(g(g-1)+g(-1)^k)$
-- statement:
--   Let $g$ be even. For every integer $k$,
--   $$
--   \sum_{j=1}^{g-1}(g-j)\,\mathbb 1\{j-k\ \text{odd}\}=\frac14\Bigl(g(g-1)+g(-1)^k\Bigr).
--   $$
--   It evaluates the bound of Lemma 4.19 summed against the weights $g-j$ in Proposition 4.14.
--
--   Differences from the source:
--   - generalization: k ∈ {1, …, n − 1} (the lemma's use in Proposition 4.14) → every integer k; reason: the printed lemma states no range for k; specializes to the paper's use
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, Lemma 4.20, p.24

import Mathlib

namespace TSPSDPGap

/-- **Lemma 4.20: a weighted parity count.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, Lemma 4.20, p.24:
"For g even, Σ_{j=1}^{g−1} (g − j)𝟙{j−k odd} = ¼(g(g − 1) + g(−1)^k)."

**Formalization Note.** For every even natural `g` and every integer `k`; `Σ_{j=1}^{g−1}` is the
sum over `Finset.Ico 1 g`, arithmetic in `ℝ`, `(−1)^k` an integer power. -/
theorem lemma_4_20 (g : ℕ) (hg : Even g) (k : ℤ) :
    ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * (if Odd ((j : ℤ) - k) then (1 : ℝ) else 0) =
      ((g : ℝ) * ((g : ℝ) - 1) + (g : ℝ) * (-1 : ℝ) ^ k) / 4 := by sorry

end TSPSDPGap
