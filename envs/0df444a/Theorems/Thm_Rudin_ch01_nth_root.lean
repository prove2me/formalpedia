-- Prove2me | Theorems.Thm_Rudin_ch01_nth_root
-- name    : Rudin.ch01_nth_root
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T18:40:47.296511+00:00
-- url     : https://prove2.me/theorems/f9cb9436-6e35-42e4-9bc8-1d81cbf4ba4a
-- title:
--   Theorem 1.21 — existence and uniqueness of positive $n$-th roots
-- statement:
--   For every real $x > 0$ and every integer $n > 0$ there is exactly one positive real $y$ with $y^n = x$; this $y$ is written $x^{1/n}$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 1, p. 10, Theorem 1.21

import Mathlib

namespace Rudin

/-- Rudin, Theorem 1.21: for every real `x > 0` and every integer `n > 0` there is exactly one
positive real `y` with `y ^ n = x`. -/
theorem ch01_nth_root (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : 0 < n) :
    ∃! y : ℝ, 0 < y ∧ y ^ n = x := by sorry

end Rudin
