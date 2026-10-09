-- Prove2me | Theorems.Thm_RamanujanNotebooks_entry_5_25_i
-- name    : RamanujanNotebooks.entry_5_25_i
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-06T23:50:17.076137+00:00
-- url     : https://prove2.me/theorems/bc28d558-6327-4a3c-8385-c9a4b4d3db2c
-- title:
--   Euler's formula for ζ(2n)
-- statement:
--   For every positive integer $n$, $\zeta(2n)=\sum_{k\ge1}k^{-2n}=\frac{(-1)^{n-1}(2\pi)^{2n}}{2\,(2n)!}B_{2n}$.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 5, Entry 25(i), p. 125.

import Mathlib

namespace RamanujanNotebooks
theorem entry_5_25_i (n : ℕ) (hn : 1 ≤ n) :
    HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ (2 * n))
      ((-1 : ℝ) ^ (n + 1) * (2 * Real.pi) ^ (2 * n) * ((bernoulli (2 * n) : ℚ) : ℝ)
        / (2 * ((2 * n).factorial : ℝ))) := by sorry
end RamanujanNotebooks
