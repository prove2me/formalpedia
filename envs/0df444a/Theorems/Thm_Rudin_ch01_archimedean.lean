-- Prove2me | Theorems.Thm_Rudin_ch01_archimedean
-- name    : Rudin.ch01_archimedean
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T18:29:33.747891+00:00
-- url     : https://prove2.me/theorems/0d07ef31-6a04-4c2d-8fbc-033e6fba9a9e
-- title:
--   Theorem 1.20(a) — the archimedean property of $\mathbb{R}$
-- statement:
--   For all real $x, y$ with $x > 0$ there is a positive integer $n$ such that $nx > y$. Equivalently, $\mathbb{R}$ has no infinitely large or infinitely small elements relative to a fixed positive $x$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 1, p. 9, Theorem 1.20(a)

import Mathlib

namespace Rudin

/-- Rudin, Theorem 1.20(a) (the archimedean property of `ℝ`): if `x > 0` and `y` is real,
then there is a positive integer `n` with `n * x > y`. -/
theorem ch01_archimedean (x y : ℝ) (hx : 0 < x) : ∃ n : ℕ, 0 < n ∧ y < n * x := by sorry

end Rudin
