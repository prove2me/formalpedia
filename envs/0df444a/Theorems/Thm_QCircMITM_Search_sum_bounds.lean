-- Prove2me | Theorems.Thm_QCircMITM_Search_sum_bounds
-- name    : QCircMITM.Search.sum_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:38:27.327596+00:00
-- url     : https://prove2.me/theorems/cb04b7e9-3e90-468c-bf49-810d49b67834
-- title:
--   §3, pp. 6–7 — the two sum bounds of the running time (corrected: 1/(|V| − 1); the printed 1/(|V|^⌈l/2⌉ − 1) fails for ⌈l/2⌉ ≥ 2)
-- statement:
--   Let $m \ge 2$ be an integer (it stands for $|\mathcal V_{n,\mathcal G}|$) and $h \ge 0$ (it stands for $\lceil l/2\rceil$). Then
--   $$\sum_{i=1}^{h} m^i \log_2(m^i) \;\le\; \sum_{i=1}^{h} m^i \log_2(m^h)$$
--   and
--   $$\sum_{i=1}^{h} m^i \;\le\; m^h\Big(1 + \frac{1}{m-1}\Big).$$
--
--   Together with $|S_i| \le m^i$ these bound the total work of MITM-factor by a constant times $m^h \log(m^h)$.
--
--   **Formalization Note.** The paper prints the second bound as $m^h\big(1 + \frac{1}{m^h - 1}\big)$, which is false for $h \ge 2$: for $m = 2$, $h = 2$ the left side is $6$ and the printed right side is $16/3$. The bound stated here, with $\frac{1}{m-1}$, is the geometric-series bound and is what the $O$-claim needs. Logarithms are `Real.logb 2`; the base does not affect the inequalities.
-- source:
--   Amy, Maslov, Mosca, Roetteler, A meet-in-the-middle algorithm for fast synthesis of depth-optimal quantum circuits, arXiv:1206.0758v3, pp. 6–7, §3, running-time paragraph

import Mathlib

namespace QCircMITM.Search

theorem sum_bounds (m : ℕ) (hm : 2 ≤ m) (h : ℕ) :
    ∑ i ∈ Finset.Icc 1 h, (m : ℝ) ^ i * Real.logb 2 ((m : ℝ) ^ i) ≤
        ∑ i ∈ Finset.Icc 1 h, (m : ℝ) ^ i * Real.logb 2 ((m : ℝ) ^ h) ∧
      ∑ i ∈ Finset.Icc 1 h, (m : ℝ) ^ i ≤ (m : ℝ) ^ h * (1 + 1 / ((m : ℝ) - 1)) := by sorry

end QCircMITM.Search
