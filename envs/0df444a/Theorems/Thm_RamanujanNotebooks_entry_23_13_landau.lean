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
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part IV (Springer, 1994), Chapter 23, Entry 13, p. 60, eq. (13.1).

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
