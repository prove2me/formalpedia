-- Prove2me | Theorems.Thm_PellEquation_xn_sub_one_mul
-- name    : PellEquation.xn_sub_one_mul
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:26:09.01385+00:00
-- url     : https://prove2.me/theorems/c9704abd-a9a5-45b8-a55d-5eaecab08c52
-- title:
--   A Pell identity for $x_m - 1$
-- statement:
--   **A factored form of the Pell equation.**
--
--   Let $a > 1$ and let $(x_m, y_m)$ be the $m$-th solution of the Pell equation
--   $x^{2} - (a^{2}-1)y^{2} = 1$, so that $x_m + y_m\sqrt{a^2-1} = (a + \sqrt{a^2-1})^{m}$. Then
--
--   $$(x_m - 1)\,(x_m - 1 + 2) \;=\; (a^{2}-1)\,y_m^{2}.$$
--
--   The left-hand side is $(x_m-1)(x_m+1) = x_m^{2}-1$, so the identity is exactly the Pell
--   equation itself, rewritten so that the factor $x_m - 1$ appears explicitly. Writing it this way
--   exposes $x_m - 1$ as a divisor of $(a^2-1)y_m^2$, which is what one needs when analysing the
--   divisibility of Pell solutions — for instance showing that a prime dividing $a$ cannot divide
--   $y_m$ for odd $m$, or extracting square factors from $x_m - 1$.
--
--   Pell solutions grow exponentially and satisfy the linear recurrences
--   $x_{m+1} = 2a x_m - x_{m-1}$, $y_{m+1} = 2a y_m - y_{m-1}$, which makes them a standard source
--   of explicit integer sequences with prescribed divisibility — the mechanism behind
--   Matiyasevich's resolution of Hilbert's tenth problem, and behind elementary constructions of
--   integers with controlled prime factorisations.
--
--   **Formalization note.** `Pell.xn` and `Pell.yn` are Mathlib's Pell solutions for the equation
--   $x^2 - (a^2-1)y^2 = 1$; the expression $x_m - 1 + 2$ is written that way to stay within
--   $\mathbb{N}$, where $x_m \ge 1$ makes the truncated subtraction exact.
-- source:
--   Classical; see Mathlib's `Mathlib/NumberTheory/Pell.lean` and Matiyasevich's work on Hilbert's tenth problem. Lean proof extracted from `Salt/MR/StridePrizePell.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace PellEquation

theorem xn_sub_one_mul {a : ℕ} (a1 : 1 < a) (m : ℕ) :
    (Pell.xn a1 m - 1) * (Pell.xn a1 m - 1 + 2)
      = (a ^ 2 - 1) * (Pell.yn a1 m * Pell.yn a1 m) := by sorry

end PellEquation
