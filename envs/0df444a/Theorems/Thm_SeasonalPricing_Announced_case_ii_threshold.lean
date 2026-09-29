-- Prove2me | Theorems.Thm_SeasonalPricing_Announced_case_ii_threshold
-- name    : SeasonalPricing.Announced.case_ii_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:12:59.183534+00:00
-- url     : https://prove2.me/theorems/c000059d-f8e7-42a8-b37a-8119b9f7b338
-- title:
--   Proof of Theorem 2, case (ii): if $e^{-\alpha(T-t)} > p_2/p_1$, the threshold is $(p_1 - wp_2)/(1 - we^{-\alpha(T-t)}) \ge p_1$
-- statement:
--   Fix an announced price path with $0 < p_1$ and $p_2 \le p_1$, a decline factor $\alpha \ge 0$, a discount time $T$, an arrival time $0 \le t < T$, and an availability probability $w \in [0, 1]$ with $w e^{-\alpha(T-t)} < 1$. Suppose
--
--   $$
--   e^{-\alpha(T-t)} > \frac{p_2}{p_1}.
--   $$
--
--   Then
--
--   $$
--   \frac{p_1 - w p_2}{1 - w e^{-\alpha(T-t)}} \ge p_1,
--   $$
--
--   and, for every base valuation $V$, the customer buys immediately (the current surplus $V(t) - p_1$ is nonnegative and at least the expected surplus of waiting $w\max\{V(T) - p_2, 0\}$) if and only if
--
--   $$
--   V(t) \ge \frac{p_1 - w p_2}{1 - w e^{-\alpha(T-t)}}.
--   $$
--
--   This is the second case of the proof of Theorem 2 of Aviv and Pazgal: when the announced discount is deep relative to the decline in valuations, the threshold rises above $p_1$ by an amount that grows with the availability $w$.
--
--   **Formalization Note** $V(t) = Ve^{-\alpha t}$ and $V(T) = Ve^{-\alpha T}$. The hypothesis $w e^{-\alpha(T-t)} < 1$ is an addition: it keeps the denominator positive (it fails only when $w = 1$ and $\alpha = 0$, where the paper's fraction is undefined). $0 < p_1$ makes the ratio $p_2/p_1$ meaningful.
-- source:
--   Aviv and Pazgal, Optimal Pricing of Seasonal Products in the Presence of Forward-Looking Consumers, Manufacturing & Service Operations Management 10(3), 2008, p. 358, Proof of Theorem 2, case (ii)

import Mathlib
import Definitions.Def_SeasonalPricing_Announced_purchaseRule

namespace SeasonalPricing.Announced

theorem case_ii_threshold (α T p1 p2 w t : ℝ) (hα : 0 ≤ α) (ht0 : 0 ≤ t) (htT : t < T)
    (hp1 : 0 < p1) (hp : p2 ≤ p1) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hwδ : w * Real.exp (-(α * (T - t))) < 1)
    (hcase : p2 / p1 < Real.exp (-(α * (T - t)))) :
    p1 ≤ (p1 - w * p2) / (1 - w * Real.exp (-(α * (T - t)))) ∧
      ∀ V : ℝ, buysNow α T p1 p2 w t V ↔
        (p1 - w * p2) / (1 - w * Real.exp (-(α * (T - t)))) ≤ valuation α V t := by sorry

end SeasonalPricing.Announced
