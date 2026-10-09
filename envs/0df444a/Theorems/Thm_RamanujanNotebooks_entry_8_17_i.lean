-- Prove2me | Theorems.Thm_RamanujanNotebooks_entry_8_17_i
-- name    : RamanujanNotebooks.entry_8_17_i
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-07T00:04:38.212575+00:00
-- url     : https://prove2.me/theorems/8c7a4267-bb41-4e83-ab8a-944e79be7123
-- title:
--   Asymptotic expansion of ∑ Log k/k
-- statement:
--   Entry 17(i), pp. 196-197: with φ(n) = ∑_{k=1}^{n} Log k / k, c_1 as in (17.2) and H_m = ∑_{k=1}^{m} 1/k, as n → ∞, φ(n) - ψ(n + 1) Log n ~ -(1/2) Log^2 n + c_1 + ∑_{k ≥ 1} B_{2k} H_{2k-1}/(2k n^{2k}). Stated for the integer variable n, as an asymptotic series: for every M, the difference between the left side and the right side cut after M terms of the sum is O(n^{-2M-2}). The term k : ℕ below is the book's term k + 1. Differs from the printed source: the asymptotic series is stated for the integer variable, one bound for each truncation order, with c_1 supplied by hypothesis.
--
--   **Discrepancy from the printed source.** The book writes ~ with x → ∞. Stated for integer n and every truncation M with error O(n^{−2M−2}); c_1 enters as a real number with the hypothesis that (17.2) converges to it. The integer variable and the truncation form are our rendering. Audit (Codex, independent): ok; for M = 1 the residual times n^4 at n = 100, 300, 1000, 3000 approaches −0.01527778.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 8, Entry 17(i), p. 196, eq. (17.1)-(17.3).

import Mathlib

namespace RamanujanNotebooks
theorem entry_8_17_i (c₁ : ℝ)
    (hc : Filter.Tendsto
      (fun n : ℕ => (∑ k ∈ Finset.range n, Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1))
        - Real.log (n : ℝ) ^ 2 / 2) Filter.atTop (nhds c₁))
    (M : ℕ) :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => (∑ k ∈ Finset.range n, Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1))
        - logDeriv Real.Gamma ((n : ℝ) + 1) * Real.log (n : ℝ)
        - (-(Real.log (n : ℝ) ^ 2) / 2 + c₁
            + ∑ k ∈ Finset.range M, (bernoulli (2 * k + 2) : ℝ)
                * (∑ j ∈ Finset.range (2 * k + 1), 1 / ((j : ℝ) + 1))
                / ((2 * (k : ℝ) + 2) * (n : ℝ) ^ (2 * k + 2))))
      (fun n : ℕ => 1 / (n : ℝ) ^ (2 * M + 2)) := by sorry
end RamanujanNotebooks
