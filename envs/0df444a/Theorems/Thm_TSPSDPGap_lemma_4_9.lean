-- Prove2me | Theorems.Thm_TSPSDPGap_lemma_4_9
-- name    : TSPSDPGap.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:37:43.088511+00:00
-- url     : https://prove2.me/theorems/ff6870af-6128-4126-8eea-afd39a30bf99
-- title:
--   Lemma 4.9 — two weighted sums for even $g$
-- statement:
--   Let $g$ be even. Then
--   $$
--   \sum_{j=1}^{g-1}(g-j)\,\mathbb 1\{j\ \text{odd}\}=\frac{g^2}{4}\qquad\text{and}\qquad\sum_{j=1}^{g-1}(g-j)(-1)^j=-\frac g2 .
--   $$
--   Both identities enter the computation of $\sum_i a_i$ (Lemma 4.10) and the eigenvalue bounds of Proposition 4.14.
--
--   Differences from the source: none.
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, Lemma 4.9, p.17

import Mathlib

namespace TSPSDPGap

/-- **Lemma 4.9: two weighted alternating sums.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, Lemma 4.9, p.17:
"Let g be even. Then Σ_{j=1}^{g−1} (g − j)𝟙{j odd} = g²/4 and Σ_{j=1}^{g−1} (g − j)(−1)^j = −g/2."

**Formalization Note.** `Σ_{j=1}^{g−1}` is the sum over `Finset.Ico 1 g`; `g − j` is computed
in `ℝ`; `𝟙{j odd}` is `if Odd j then 1 else 0`. -/
theorem lemma_4_9 (g : ℕ) (hg : Even g) :
    ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * (if Odd j then (1 : ℝ) else 0) = (g : ℝ) ^ 2 / 4 ∧
    ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * (-1 : ℝ) ^ j = -(g : ℝ) / 2 := by sorry

end TSPSDPGap
