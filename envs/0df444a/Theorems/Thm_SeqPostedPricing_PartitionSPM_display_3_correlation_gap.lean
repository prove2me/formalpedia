-- Prove2me | Theorems.Thm_SeqPostedPricing_PartitionSPM_display_3_correlation_gap
-- name    : SeqPostedPricing.PartitionSPM.display_3_correlation_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:14:34.702033+00:00
-- url     : https://prove2.me/theorems/f26b7941-d3c1-488b-923c-10450c403963
-- title:
--   Display (3): $1-\prod_i(1-q_i) \ge 1-(1-s/n)^n \ge (1-1/e)s$
-- statement:
--   Let $q_1, \dots, q_n \in [0,1]$ with $\sum_i q_i = s \le 1$. Then
--
--   $$
--   1 - \prod_{i=1}^n (1 - q_i) \;\ge\; 1 - \Big(1 - \frac{s}{n}\Big)^n \;\ge\; \Big(1 - \frac1e\Big) s .
--   $$
--
--   Multiplied by the common price $p \ge 0$, the left side is the revenue $R^{\mathcal S}_{eq}$ of the equal-price SPM in a single-item auction, and the chain shows $R^{\mathcal S}_{eq} \ge (1 - 1/e)\, p s$.
--
--   **Formalization Note** For $n = 0$ all three quantities are $0$.
--
--   Differences from the source:
--   - encoding: p(1 − Π(1 − q_i)) ≥ p(1 − Π_{i=1}^n (1 − s/n)) ≥ (1 − 1/e)ps → the same two inequalities with the common price p ≥ 0 factored out; reason: multiplying by p ≥ 0 preserves both inequalities; the statements are equivalent for p > 0
--   - encoding: Π_{i=1}^n (1 − s/n) and 1/e → (1 − s/n)^n and Real.exp (−1); reason: the same numbers
--   - encoding: agents 1, …, n → `Fin n`; reason: Lean indexing convention; the same instances
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, proof of Theorem 21, display (3), p. 15 (PDF p. 17)

import Mathlib

namespace SeqPostedPricing.PartitionSPM

/-- **Display (3)** (Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, proof of Theorem 21, display (3), p. 15 = PDF p. 17):
"R^S_eq = p(Pr[Some agent is served]) = p(1 − Pr[No agent is served]) = p(1 − Π_{i=1}^n (1 − qi))
≥ p(1 − Π_{i=1}^n (1 − s/n)) (3) ≥ (1 − 1/e)ps, where (3) follows since the product is maximized when
the qi's are all equal."

For probabilities `q_1, …, q_n ∈ [0, 1]` with sum `s ≤ 1`,
`1 − (1 − s/n)^n ≤ 1 − Π_i (1 − q_i)` and `(1 − 1/e) s ≤ 1 − (1 − s/n)^n`.

**Formalization Note** The common price `p ≥ 0` is factored out of both inequalities (Reading 7).
`Π_{i=1}^n (1 − s/n)` is written `(1 − s/n)^n`. At `n = 0` all three quantities are `0`. -/
theorem display_3_correlation_gap {n : ℕ} (q : Fin n → ℝ) (s : ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (hs : ∑ i, q i = s) (hs1 : s ≤ 1) :
    1 - (1 - s / n) ^ n ≤ 1 - ∏ i, (1 - q i) ∧
      (1 - Real.exp (-1)) * s ≤ 1 - (1 - s / n) ^ n := by sorry

end SeqPostedPricing.PartitionSPM
