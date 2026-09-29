-- Prove2me | Theorems.Thm_Rudin_ch01_rationals_dense
-- name    : Rudin.ch01_rationals_dense
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T18:39:41.446152+00:00
-- url     : https://prove2.me/theorems/ddcdfe50-bda3-488e-a6d0-cef30014d4c8
-- title:
--   Theorem 1.20(b) — $\mathbb{Q}$ is dense in $\mathbb{R}$
-- statement:
--   If $x < y$ are real numbers, there is a rational $p$ with $x < p < y$: between any two distinct reals lies a rational number.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 1, p. 9, Theorem 1.20(b)

import Mathlib

namespace Rudin

/-- Rudin, Theorem 1.20(b): `ℚ` is dense in `ℝ`; between any two reals `x < y` there is a
rational number `p` with `x < p < y`. -/
theorem ch01_rationals_dense (x y : ℝ) (hxy : x < y) :
    ∃ p : ℚ, x < (p : ℝ) ∧ (p : ℝ) < y := by sorry

end Rudin
