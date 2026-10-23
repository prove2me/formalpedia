-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartIV_entry_7_3_1_a
-- name    : RamanujanLostNotebook.PartIV.entry_7_3_1_a
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-06T13:03:28.834161+00:00
-- url     : https://prove2.me/theorems/4d6b5022-f980-4cb2-b6c2-0dd5c539f6c0
-- title:
--   Small fractional parts of N e^{2/a} occur infinitely often
-- statement:
--   Let $a$ be a nonzero integer and $\epsilon>0$. Then there are infinitely many integers $N\ge3$ with $Ne^{2/a}-\lfloor Ne^{2/a}\rfloor<\frac{(1+\epsilon)\log\log N}{|a|N\log N}$. Differs from the printed source: the book (p. 176, (7.3.1)) asks for infinitely many positive integers N; we restrict the set to N ≥ 3 so that log log N > 0 and no logarithm of 0 or division by log 1 = 0 occurs. Evidence: discarding finitely many N does not affect infinitude (a proof of equivalence, given positivity for N ≥ 3). The guard is ours.
--
--   **Discrepancy from the printed source.** Book, p. 176, (7.3.1): infinitely many positive integers N satisfy the inequality. Stated here: the set of N ≥ 3 satisfying it is infinite. For N = 1, 2 the printed right side is undefined or negative (log 1 = 0, log log 2 < 0), so restricting to N ≥ 3 removes only junk cases. Evidence: logical equivalence up to finitely many N (proof). Who: us.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013, Chapter 7, Entry 7.3.1, p. 176, eq. (7.3.1).

import Mathlib

namespace RamanujanLostNotebook.PartIV
theorem entry_7_3_1_a (a : ℤ) (ha : a ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    Set.Infinite {N : ℕ | 3 ≤ N ∧
      (N : ℝ) * Real.exp (2 / (a : ℝ)) - (Int.floor ((N : ℝ) * Real.exp (2 / (a : ℝ))) : ℝ)
        < (1 + ε) * Real.log (Real.log (N : ℝ)) / (abs (a : ℝ) * (N : ℝ) * Real.log (N : ℝ))} := by sorry
end RamanujanLostNotebook.PartIV
