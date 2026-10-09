-- Prove2me | Theorems.Thm_RamanujanNotebooks_entry_2_1
-- name    : RamanujanNotebooks.entry_2_1
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-06T21:07:47.798279+00:00
-- url     : https://prove2.me/theorems/90bece59-846f-42f6-8ff9-7cefdac3b2eb
-- title:
--   Sum of 1/(n+k) in terms of 1/((2k)^3 - 2k)
-- statement:
--   For every positive integer $n$, $$\sum_{k=1}^{n}\frac1{n+k}=\frac{n}{2n+1}+\sum_{k=1}^{n}\frac1{(2k)^3-2k}.$$
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 2, Entry 1, p. 25, eq. (1.1).

import Mathlib

namespace RamanujanNotebooks
theorem entry_2_1 (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.range n, (1 : ℚ) / ((n : ℚ) + ((k : ℚ) + 1))) =
      (n : ℚ) / (2 * (n : ℚ) + 1) +
        (∑ k ∈ Finset.range n, (1 : ℚ) / ((2 * ((k : ℚ) + 1)) ^ 3 - 2 * ((k : ℚ) + 1))) := by sorry
end RamanujanNotebooks
