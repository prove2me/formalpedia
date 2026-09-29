-- Prove2me | Theorems.Thm_Rudin_ch01_cauchy_schwarz
-- name    : Rudin.ch01_cauchy_schwarz
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T18:42:24.735807+00:00
-- url     : https://prove2.me/theorems/d9b7f880-3a06-4a09-b9d7-8833a42c6528
-- title:
--   Theorem 1.35 — the Schwarz inequality
-- statement:
--   For complex numbers $a_1, \dots, a_n$ and $b_1, \dots, b_n$, $$\Big|\sum_{j=1}^n a_j \overline{b_j}\Big|^2 \le \sum_{j=1}^n |a_j|^2 \sum_{j=1}^n |b_j|^2 .$$
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 1, p. 15, Theorem 1.35

import Mathlib

namespace Rudin

/-- Rudin, Theorem 1.35 (the Schwarz inequality): for complex numbers `a 0, …, a (n-1)` and
`b 0, …, b (n-1)`,
`|∑ a j * conj (b j)| ^ 2 ≤ (∑ |a j| ^ 2) * (∑ |b j| ^ 2)`. -/
theorem ch01_cauchy_schwarz (n : ℕ) (a b : Fin n → ℂ) :
    ‖∑ j, a j * (starRingEnd ℂ) (b j)‖ ^ 2 ≤ (∑ j, ‖a j‖ ^ 2) * (∑ j, ‖b j‖ ^ 2) := by sorry

end Rudin
