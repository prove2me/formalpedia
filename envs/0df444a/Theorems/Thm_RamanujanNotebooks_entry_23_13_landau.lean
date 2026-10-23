-- Prove2me | Theorems.Thm_RamanujanNotebooks_entry_23_13_landau
-- name    : RamanujanNotebooks.entry_23_13_landau
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-06T23:06:35.418026+00:00
-- url     : https://prove2.me/theorems/517a1e54-d391-4ece-a681-73193ddb5baa
-- title:
--   Landau's theorem on sums of two squares
-- statement:
--   Let $B(x)$ be the number of positive integers $\le x$ that are sums of two squares and $K=\bigl(\tfrac12\prod_{p\equiv3\ (4)}(1-p^{-2})^{-1}\bigr)^{1/2}$. Then $B(x)\sqrt{\log x}/x\to K$ as $x\to\infty$.
--
--   **Discrepancy from the printed source.** Entry 13 (p. 60) approximates the count of sums of two squares in an interval from A to B by K times an integral. Stated here instead is the cumulative limit $B(x)\sqrt{\log x}/x\to K$, which Berndt credits to Landau on pp. 61–62; $K$ is given by (13.1) on p. 60. The product over primes $p\equiv3\pmod4$ enters through a hypothesis fixing its value $P$, and $K=\sqrt{P/2}$.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part IV (Springer, 1994), Chapter 23, Discussion of Entry 13, pp. 61–62; constant (13.1), p. 60.

import Mathlib
import Definitions.Def_RamanujanNotebooks_ch23_ch23SumTwoSqCount

namespace RamanujanNotebooks
theorem entry_23_13_landau
    (P : ℝ)
    (hP : HasProd (fun p : Nat.Primes =>
      if (p : ℕ) % 4 = 3 then (1 - (((p : ℕ) : ℝ) ^ 2)⁻¹)⁻¹ else 1) P) :
    Filter.Tendsto
      (fun x : ℝ => (ch23SumTwoSqCount x : ℝ) * Real.sqrt (Real.log x) / x)
      Filter.atTop (nhds (Real.sqrt (P / 2))) := by sorry
end RamanujanNotebooks
