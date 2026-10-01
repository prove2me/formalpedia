-- Prove2me | Theorems.Thm_SmaleMeanValue_extremal_example
-- name    : SmaleMeanValue.extremal_example
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T21:45:43.363008+00:00
-- url     : https://prove2.me/theorems/20c19bcb-6e40-4e22-b7f4-413d8e457571
-- title:
--   The extremal example $z^d - dz$
-- statement:
--   Let $d \ge 2$ be an integer and $P(z) = z^d - dz$. Then
--
--   1. $P$ has degree exactly $d$;
--   2. $P'(0) \neq 0$;
--   3. every critical point $c$ of $P$ satisfies
--   $$
--   \left| \frac{P(0) - P(c)}{0 - c} \right| = \frac{d-1}{d}\,|P'(0)|.
--   $$
--
--   Consequently, in degree $d$ the constant $K$ in the mean value problem cannot be smaller than $\frac{d-1}{d}$: for this polynomial and $z = 0$ every critical point attains exactly that ratio.
-- source:
--   Wikipedia, "Mean value problem", revision oldid=1374678764, https://en.wikipedia.org/w/index.php?title=Mean_value_problem&oldid=1374678764, lead section ("the constant K has to be at least (d-1)/d due to the example P(z) = z^d - dz")

import Mathlib
open Polynomial

namespace SmaleMeanValue

theorem extremal_example (d : ℕ) (hd : 2 ≤ d) :
    (X ^ d - C (d : ℂ) * X : ℂ[X]).natDegree = d ∧
    (X ^ d - C (d : ℂ) * X : ℂ[X]).derivative.eval 0 ≠ 0 ∧
    ∀ c : ℂ, (X ^ d - C (d : ℂ) * X : ℂ[X]).derivative.eval c = 0 →
      ‖((X ^ d - C (d : ℂ) * X : ℂ[X]).eval 0 - (X ^ d - C (d : ℂ) * X : ℂ[X]).eval c)
          / (0 - c)‖
        = (((d : ℝ) - 1) / d) * ‖(X ^ d - C (d : ℂ) * X : ℂ[X]).derivative.eval 0‖ := by sorry

end SmaleMeanValue
