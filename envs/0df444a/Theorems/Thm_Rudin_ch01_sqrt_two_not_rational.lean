-- Prove2me | Theorems.Thm_Rudin_ch01_sqrt_two_not_rational
-- name    : Rudin.ch01_sqrt_two_not_rational
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T18:04:55.346086+00:00
-- url     : https://prove2.me/theorems/55d7337a-4fc3-43ba-b704-c8d3cce8d8c0
-- title:
--   Irrationality of $\sqrt{2}$
-- statement:
--   No rational number has square $2$: there is no $p \in \mathbb{Q}$ with $p^2 = 2$. This is the observation with which Rudin opens the book; it is the concrete gap in $\mathbb{Q}$ that motivates the construction of the real field.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 1, pp. 1-2, Example 1.1

import Mathlib

namespace Rudin

/-- Rudin, Example 1.1: there is no rational number whose square is `2`. -/
theorem ch01_sqrt_two_not_rational : ¬ ∃ p : ℚ, p ^ 2 = 2 := by sorry

end Rudin
