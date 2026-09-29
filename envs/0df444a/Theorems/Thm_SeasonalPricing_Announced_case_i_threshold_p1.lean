-- Prove2me | Theorems.Thm_SeasonalPricing_Announced_case_i_threshold_p1
-- name    : SeasonalPricing.Announced.case_i_threshold_p1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:12:33.501293+00:00
-- url     : https://prove2.me/theorems/797e9c63-b571-4e46-90c6-557585fa7af3
-- title:
--   Proof of Theorem 2, case (i): if $e^{-\alpha(T-t)} \le p_2/p_1$, the premium price $p_1$ is the purchase threshold
-- statement:
--   Fix an announced price path with $0 < p_1$ and $p_2 \le p_1$, a decline factor $\alpha \ge 0$, a discount time $T$, an arrival time $0 \le t < T$, and an availability probability $w \in [0, 1]$. Suppose
--
--   $$
--   e^{-\alpha(T-t)} \le \frac{p_2}{p_1}.
--   $$
--
--   Then, for every base valuation $V$, the customer buys immediately (the current surplus $V(t) - p_1$ is nonnegative and at least the expected surplus of waiting $w\max\{V(T) - p_2, 0\}$) if and only if
--
--   $$
--   V(t) \ge p_1 .
--   $$
--
--   This is the first case of the proof of Theorem 2 of Aviv and Pazgal: when the announced discount is shallow relative to the decline in valuations, waiting never pays and the premium price itself is the threshold.
--
--   **Formalization Note** $V(t) = Ve^{-\alpha t}$ and $V(T) = Ve^{-\alpha T}$. The hypothesis $0 < p_1$ makes the paper's ratio $p_2/p_1$ meaningful; the paper uses it without stating it. The conclusion holds for every $w \in [0,1]$, as in the paper's proof.
-- source:
--   Aviv and Pazgal, Optimal Pricing of Seasonal Products in the Presence of Forward-Looking Consumers, Manufacturing & Service Operations Management 10(3), 2008, p. 358, Proof of Theorem 2, case (i)

import Mathlib
import Definitions.Def_SeasonalPricing_Announced_purchaseRule

namespace SeasonalPricing.Announced

theorem case_i_threshold_p1 (α T p1 p2 w t : ℝ) (hα : 0 ≤ α) (ht0 : 0 ≤ t) (htT : t < T)
    (hp1 : 0 < p1) (hp : p2 ≤ p1) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hcase : Real.exp (-(α * (T - t))) ≤ p2 / p1) (V : ℝ) :
    buysNow α T p1 p2 w t V ↔ p1 ≤ valuation α V t := by sorry

end SeasonalPricing.Announced
